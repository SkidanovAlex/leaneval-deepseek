import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.PT.shapiro_defs
import Submission.Work.SSGRoute.PT.shapiro_H2_coind
import Submission.Work.SSGRoute.PT.shapiro_H0_coind
import Submission.Work.SSGRoute.PT.frobenius_coindAux
import Submission.Work.SSGRoute.PT.AlphaPairing
import Submission.Work.SSGRoute.PT.alphaTwo_evalHom
import Submission.Work.SSGRoute.PT.AlphaTwoKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base case of Milne's `α²`-dévissage: the trace and the corestriction

Milne's dévissage of `Work.SSGRoute.PT.alphaTwo_bijective_of_devissage` starts from the module
`N₂ = Coind^G_U M` coinduced from an open subgroup `U ≤ G` acting trivially on the finite module
`M` (so that `α²(G, N₂)` is the *trivial-action* instance over `U`).  This file builds the
structural comparison used there:

* `trace` — the **trace** `Σ : Coind^G_U D →+ D`, `Σ f = ∑_{C : G ⧸ U} secC C • f (secC C)`,
  which is `G`-equivariant (`trace_smul`) and independent of the chosen coset section;
* `shapiroEquiv` — Shapiro's lemma in degree `2` as a **named** additive equivalence
  `H²(G, Coind^G_U M) ≃+ H²(U, M)`, with the computation rule `shapiroEquiv_H2π`;
* `CoindMap` — functoriality of `Coind` in the coefficients (pointwise application);
* `corH2` — the **corestriction** `H²(U, D) →+ H²(G, D)` for a `G`-module `D`,
  `cor = mapH2 Σ ∘ (Shapiro)⁻¹`, with the computation rule `corH2_shapiroEquiv`.

## The remaining structural obligation (the "Shapiro/cup square")

The base case `α²(G, Coind^G_U M)` bijective is *equivalent* to the two facts

* (`α`) the Shapiro/cup compatibility: under `extShapiroH2Aux` (`H²(G, ConjHom (Coind^G_U M) C)
  ≃+ H²(U, ConjHom M C)`) and the degree-`0` Shapiro identification
  `(Coind^G_U M)^G ≅ M^U`, the `α²`-pairing of `Coind^G_U M` over `G` is `cor` composed with the
  `α²`-pairing of `M` over `U`;
* (`β`) the non-degeneracy of the corestriction on `p`-torsion: `corH2` induces an isomorphism
  `H²(U, C)[p] → H²(G, C)[p]` (equivalently: `corH2` is non-zero there — this is the *arithmetic*
  input, the compatibility of the local invariant maps `inv_U` of Milne ADT (1.1b)).

Since `α²(U, M)` is bijective (the *trivial-action* base case, `alphaTwo_trivAction_of_trivMod`),
(`α`) + (`β`) give the base case.  Note that for `[G : U]` **coprime to `p`**, (`β`) is *free*:
`corH2 ∘ res = [G : U]` with `res` an isomorphism on `p`-torsion.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Classical
open scoped BigOperators

namespace Work.SSGRoute.PT

noncomputable section

universe u

variable {G : Type u} [Group G] (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)]

/-! ## The trace -/

/-- **The trace** `Σ : Coind^G_U D →+ D` for a `G`-module `D`,
`Σ f = ∑_{C : G ⧸ U} secC C • f (secC C)`. -/
def trace (D : Type u) [AddCommGroup D] [DistribMulAction G D] : Coind G U D →+ D where
  toFun f := ∑ C : G ⧸ U, secC U C • f (secC U C)
  map_zero' := by
    simp
  map_add' f h := by
    have hpt : ∀ x : G, (↑(f + h) : G → D) x = (f : G → D) x + (h : G → D) x := fun x => rfl
    simp only [hpt, smul_add]
    exact Finset.sum_add_distrib

@[simp] theorem trace_apply (D : Type u) [AddCommGroup D] [DistribMulAction G D]
    (f : Coind G U D) :
    trace U D f = ∑ C : G ⧸ U, secC U C • f (secC U C) := rfl

/-- The `U`-coordinate of `g⁻¹` at the coset `C`, i.e. `u` with `g⁻¹ * secC (g • C)
= secC C * u`. -/
def traceAux (g : G) (C : G ⧸ U) : U := Shapiro.A 0 G U g⁻¹ C

/-- The defining relation of `traceAux`. -/
theorem traceAux_spec (g : G) (C : G ⧸ U) :
    g⁻¹ * secC U (g • C) = secC U C * (traceAux U g C : G) := by
  have h := Shapiro.sec_mul_A 0 G U g⁻¹ C
  simp only [inv_inv] at h
  simpa [secC, traceAux] using h

/-- The "inverse" form of the defining relation of `traceAux`. -/
theorem traceAux_inv_spec (g : G) (C : G ⧸ U) :
    secC U (g • C) * (((traceAux U g C : U) : G))⁻¹ = g * secC U C := by
  have h : secC U (g • C) = g * (secC U C * (traceAux U g C : G)) := by
    rw [← traceAux_spec U g C]
    group
  rw [h]
  group

/-- **The summand identity** behind the equivariance of the trace. -/
theorem trace_smul_aux (D : Type u) [AddCommGroup D] [DistribMulAction G D]
    (g : G) (f : Coind G U D) (C : G ⧸ U) :
    secC U (g • C) • f (g⁻¹ * secC U (g • C)) = (g * secC U C) • f (secC U C) := by
  have hf : f (g⁻¹ * secC U (g • C)) = (traceAux U g C)⁻¹ • f (secC U C) := by
    rw [traceAux_spec U g C, Coind.coe_mul]
  rw [hf, Subgroup.smul_def, ← mul_smul]
  congr 1
  exact traceAux_inv_spec U g C

/-- **The trace is `G`-equivariant**: `Σ (g • f) = g • Σ f`. -/
theorem trace_smul (D : Type u) [AddCommGroup D] [DistribMulAction G D]
    (g : G) (f : Coind G U D) :
    trace U D (g • f) = g • trace U D f := by
  rw [trace_apply, trace_apply]
  simp only [Coind.smul_apply]
  have hsum : ∑ C : G ⧸ U, secC U C • f (g⁻¹ * secC U C)
      = ∑ C : G ⧸ U, secC U (g • C) • f (g⁻¹ * secC U (g • C)) := by
    refine (Finset.sum_bij' (fun C (_ : C ∈ Finset.univ) => g • C)
      (fun C (_ : C ∈ Finset.univ) => g⁻¹ • C)
      (fun C _ => Finset.mem_univ _) (fun C _ => Finset.mem_univ _) ?_ ?_ ?_).symm
    · intro C _
      rw [inv_smul_smul]
    · intro C _
      rw [smul_inv_smul]
    · intro C _
      simp only [smul_inv_smul]
  rw [hsum, Finset.sum_congr rfl (fun C _ => trace_smul_aux U D g f C), Finset.smul_sum]
  exact Finset.sum_congr rfl fun C _ => (smul_smul g (secC U C) (f (secC U C))).symm

/-- The trace as an equivariant map (the form consumed by `mapH2`). -/
theorem isEquivariant_trace (D : Type u) [AddCommGroup D] [DistribMulAction G D] :
    Work.GroupCohomology.IsEquivariant G (trace U D) :=
  fun g f => trace_smul U D g f

/-! ## Functoriality of `Coind` in the coefficients -/

/-- Functoriality of the coinduced module in the coefficients (pointwise application). -/
def CoindMap {M M' : Type u} [AddCommGroup M] [AddCommGroup M'] [DistribMulAction U M]
    [DistribMulAction U M'] (θ : M →+ M')
    (hθ : Work.GroupCohomology.IsEquivariant U θ) : Coind G U M →+ Coind G U M' where
  toFun f := ⟨fun g => θ (f g), by
    intro g u
    show θ (f (g * (u : G))) = u⁻¹ • θ (f g)
    rw [Coind.coe_mul, hθ u⁻¹ (f g)]⟩
  map_zero' := by
    apply Subtype.ext
    funext g
    simp
  map_add' f h := by
    apply Subtype.ext
    funext g
    simp

@[simp] theorem CoindMap_apply {M M' : Type u} [AddCommGroup M] [AddCommGroup M']
    [DistribMulAction U M] [DistribMulAction U M'] (θ : M →+ M')
    (hθ : Work.GroupCohomology.IsEquivariant U θ) (f : Coind G U M) (g : G) :
    CoindMap U θ hθ f g = θ (f g) := rfl

/-- `CoindMap` is functorial. -/
theorem CoindMap_comp {M M' M'' : Type u} [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup M''] [DistribMulAction U M] [DistribMulAction U M']
    [DistribMulAction U M''] (θ : M →+ M') (θ' : M' →+ M'')
    (hθ : Work.GroupCohomology.IsEquivariant U θ) (hθ' : Work.GroupCohomology.IsEquivariant U θ') :
    CoindMap U (θ'.comp θ) (hθ'.comp hθ)
      = (CoindMap U θ' hθ').comp (CoindMap U θ hθ) := by
  apply AddMonoidHom.ext
  intro f
  apply Subtype.ext
  funext g
  rfl

/-- `CoindMap` is `G`-equivariant. -/
theorem isEquivariant_coindMap {M M' : Type u} [AddCommGroup M] [AddCommGroup M']
    [DistribMulAction U M] [DistribMulAction U M'] (θ : M →+ M')
    (hθ : Work.GroupCohomology.IsEquivariant U θ) :
    Work.GroupCohomology.IsEquivariant G (CoindMap U θ hθ) := by
  intro g f
  apply Subtype.ext
  funext x
  rfl

/-! ## Shapiro's lemma in degree `2`, as a named equivalence -/

/-- **Shapiro's lemma in degree `2` for the coinduced module**, as a named additive equivalence,
with the computation rule `shapiroEquiv_H2π`. -/
noncomputable def shapiroEquiv {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type u} [AddCommGroup M] [DistribMulAction U M] :
    Work.AbsoluteKummer.H2 G (Coind G U M) ≃+ Work.AbsoluteKummer.H2 U M :=
  AddEquiv.ofBijective (phiH2 U M hUo) (by
    constructor
    · intro x y hxy
      have h0 : phiH2 U M hUo (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
        ((Work.AbsoluteKummer.B2 G (Coind G U M)).comap
          (Work.AbsoluteKummer.Z2 G (Coind G U M)).subtype) (x - y)
      have hc0 : phiH2 U M hUo (Work.AbsoluteKummer.H2π G (Coind G U M) c) = 0 :=
        (congrArg (fun z => phiH2 U M hUo z) hc).trans h0
      have hker : (phiC U M ((c : Work.AbsoluteKummer.Z2 G (Coind G U M)) :
          G × G → Coind G U M)) ∈ Work.AbsoluteKummer.B2 U M := by
        rw [phiH2_mk] at hc0
        rw [Work.AbsoluteKummer.H2π_eq_zero_iff] at hc0
        exact hc0
      obtain ⟨b, hb, hbc⟩ := (Work.AbsoluteKummer.mem_B2_iff _).mp hker
      obtain ⟨B, hB, hBc⟩ := shapiro_H2_inj U hUo
        ((c : Work.AbsoluteKummer.Z2 G (Coind G U M)) : G × G → Coind G U M) c.2
        ⟨b, hb, hbc⟩
      have hzero : Work.AbsoluteKummer.H2π G (Coind G U M) c = 0 :=
        (Work.AbsoluteKummer.H2π_eq_zero_iff c).mpr
          ((Work.AbsoluteKummer.mem_B2_iff c).mpr ⟨B, hB, hBc⟩)
      exact sub_eq_zero.mp (hc.symm.trans hzero)
    · intro y
      obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective
        ((Work.AbsoluteKummer.B2 U M).comap (Work.AbsoluteKummer.Z2 U M).subtype) y
      obtain ⟨c, hc, hcl⟩ := shapiro_H2_lift U hUo
        ((a : Work.AbsoluteKummer.Z2 U M) : U × U → M) a.2
      refine ⟨Work.AbsoluteKummer.H2π G (Coind G U M) ⟨c, hc⟩, ?_⟩
      refine (phiH2_mk U M hUo ⟨c, hc⟩).trans ?_
      rw [← ha]
      congr 1
      apply Subtype.ext
      funext p
      obtain ⟨u, v⟩ := p
      show phiC U M c (u, v) = (a : U × U → M) (u, v)
      rw [phiC_apply]
      exact hcl u v)

/-- The computation rule of `shapiroEquiv`. -/
theorem shapiroEquiv_H2π {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type u} [AddCommGroup M] [DistribMulAction U M]
    (c : Work.AbsoluteKummer.Z2 G (Coind G U M)) :
    shapiroEquiv U hUo (Work.AbsoluteKummer.H2π G (Coind G U M) c)
      = Work.AbsoluteKummer.H2π U M (phiZ2 U M hUo c) :=
  phiH2_mk U M hUo c

/-! ## The corestriction -/

/-- **The corestriction** `cor : H²(U, D) →+ H²(G, D)` for a `G`-module `D`:
the inverse Shapiro isomorphism followed by the trace. -/
noncomputable def corH2 {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (D : Type u) [AddCommGroup D] [DistribMulAction G D] :
    Work.AbsoluteKummer.H2 U D →+ Work.AbsoluteKummer.H2 G D :=
  (Work.AbsoluteKummer.mapH2 (trace U D) (isEquivariant_trace U D)).comp
    (shapiroEquiv U hUo (M := D)).symm.toAddMonoidHom

/-- Defining property of `corH2`. -/
theorem corH2_apply {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (D : Type u) [AddCommGroup D] [DistribMulAction G D] (y : Work.AbsoluteKummer.H2 U D) :
    corH2 U hUo D y = Work.AbsoluteKummer.mapH2 (trace U D) (isEquivariant_trace U D)
      ((shapiroEquiv U hUo (M := D)).symm y) := rfl

/-- **The computation rule of the corestriction**: `cor ∘ Shapiro = mapH2 Σ`. -/
theorem corH2_shapiroEquiv {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (D : Type u) [AddCommGroup D] [DistribMulAction G D]
    (x : Work.AbsoluteKummer.H2 G (Coind G U D)) :
    corH2 U hUo D (shapiroEquiv U hUo (M := D) x)
      = Work.AbsoluteKummer.mapH2 (trace U D) (isEquivariant_trace U D) x := by
  rw [corH2_apply, AddEquiv.symm_apply_apply]


/-! ## Independence of the trace from the chosen coset section -/

/-- The two natural descriptions of the trace (over the chosen section `secC` and over
`Quotient.out`) agree, because a change of representative changes the summand by
`secC q = q.out * u` (`u ∈ U`) and `y` is `U`-equivariant. -/
theorem trace_section_independence (D : Type u) [AddCommGroup D] [DistribMulAction G D]
    (y : Coind G U D) :
    (∑ q : G ⧸ U, secC U q • y (secC U q)) = ∑ q : G ⧸ U, q.out • y q.out := by
  refine Finset.sum_congr rfl fun q _ => ?_
  have hmem : (q.out)⁻¹ * secC U q ∈ U :=
    (coset_eq_iff U q.out (secC U q)).mp (by rw [secC_mk U q, QuotientGroup.out_eq'])
  let u : U := ⟨(q.out)⁻¹ * secC U q, hmem⟩
  have hq : secC U q = q.out * (u : G) := by
    show secC U q = q.out * (q.out⁻¹ * secC U q)
    group
  rw [hq, Coind.coe_mul, Subgroup.smul_def, ← mul_smul]
  congr 1
  rw [Subgroup.coe_inv]
  group

/-! ## The Frobenius/Shapiro isomorphism on the coefficients -/

/-- **Frobenius reciprocity for the coinduced module**, as a named additive equivalence
`Hom_ℤ(Coind^G_U M, C) ≃+ Coind^G_U (Hom_ℤ(M,C))`; the underlying map is `psiAux`. -/
noncomputable def frobeniusEquiv {G : Type u} [Group G] (U : Subgroup G) [U.FiniteIndex]
    [Fintype (G ⧸ U)] {M : Type u} [AddCommGroup M] [DistribMulAction U M]
    {C : Type u} [AddCommGroup C] [DistribMulAction G C] :
    ConjHom (Coind G U M) C ≃+ Coind G U (ConjHom M C) :=
  ⟨Equiv.ofBijective (psiAux U) ⟨psiAux_injective U, psiAux_surjective U⟩,
    fun x y => psiAux_add U x y⟩

@[simp] theorem frobeniusEquiv_apply {G : Type u} [Group G] (U : Subgroup G) [U.FiniteIndex]
    [Fintype (G ⧸ U)] {M : Type u} [AddCommGroup M] [DistribMulAction U M]
    {C : Type u} [AddCommGroup C] [DistribMulAction G C] (Φ : ConjHom (Coind G U M) C) :
    frobeniusEquiv U Φ = psiAux U Φ := rfl

@[simp] theorem frobeniusEquiv_toAddMonoidHom_apply {G : Type u} [Group G] (U : Subgroup G)
    [U.FiniteIndex] [Fintype (G ⧸ U)] {M : Type u} [AddCommGroup M] [DistribMulAction U M]
    {C : Type u} [AddCommGroup C] [DistribMulAction G C] (Φ : ConjHom (Coind G U M) C) :
    (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom Φ = psiAux U Φ := rfl

/-- The Frobenius isomorphism is `G`-equivariant. -/
theorem isEquivariant_frobeniusEquiv {G : Type u} [Group G] (U : Subgroup G) [U.FiniteIndex]
    [Fintype (G ⧸ U)] {M : Type u} [AddCommGroup M] [DistribMulAction U M]
    {C : Type u} [AddCommGroup C] [DistribMulAction G C] :
    Work.GroupCohomology.IsEquivariant G
    (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom :=
  fun g Φ => psiAux_smul U Φ g

/-! ## The coefficient identity behind the Shapiro/cup square -/

/-- Computation rule for `CoindMap` of the coefficient map `ConjHom.evalHom m`. -/
theorem coindMap_evalHom_apply {M : Type u} [AddCommGroup M] [DistribMulAction U M]
    {C : Type u} [AddCommGroup C] [DistribMulAction G C]
    {m : M} {hm : m ∈ Work.GroupCohomology.invariants U M}
    (y : Coind G U (ConjHom M C)) (g : G) :
    CoindMap U (ConjHom.evalHom m) (fun g f => evalHom_smul m hm g f) y g = (y g) m := rfl

/-- The two natural descriptions of the trace (over the chosen section `secC` and over
`Quotient.out`) agree. -/
theorem trace_eq_out_sum (D : Type u) [AddCommGroup D] [DistribMulAction G D]
    (y : Coind G U D) :
    trace U D y = ∑ q : G ⧸ U, q.out • y q.out := by
  rw [trace_apply, trace_section_independence]

/-- **The coefficient identity (α)(ii)**, in the `Quotient.out`-sum form: evaluating at a
`G`-invariant element `n` of the coinduced module factors through the Frobenius/Shapiro map
`psiAux`, the coefficient evaluation `ConjHom.evalHom (n 1) : Hom_ℤ(M,C) →+ C` and the trace.

It holds because `n = ∑_{q ∈ G/U} θ_{q, n 1}` (`thetaAux_spanning`, `n` being constant) and
`(psiAux U Φ) g m = g⁻¹ • Φ (θ_{g,m})` (`psiAuxFun_apply`). -/
theorem evalHom_eq_out_sum
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (M : Type u) [AddCommGroup M] [DistribMulAction U M]
    (C : Type u) [AddCommGroup C] [DistribMulAction G C]
    (n : Coind G U M) (hn : n ∈ Work.GroupCohomology.invariants G (Coind G U M))
    (Φ : ConjHom (Coind G U M) C) :
    Φ n = ∑ q : G ⧸ U, q.out • ((psiAux U Φ) q.out) (n 1) := by
  have hconst : ∀ x : G, n x = n 1 := by
    intro x
    have h := (Work.GroupCohomology.mem_invariants (G := G) (A := Coind G U M) n).mp hn x⁻¹
    have h2 := congrArg (fun z : Coind G U M => z (1 : G)) h
    simpa [Coind.smul_apply] using h2
  have hspan : n = ∑ q : G ⧸ U, thetaAux U q.out (n 1) := by
    conv_lhs => rw [thetaAux_spanning U n]
    exact Finset.sum_congr rfl fun q _ => by rw [hconst q.out]
  have hterm : ∀ q : G ⧸ U,
      Φ (thetaAux U q.out (n 1)) = q.out • ((psiAux U Φ) q.out) (n 1) := by
    intro q
    rw [psiAux_apply, psiAuxFun_apply, smul_smul, mul_inv_cancel, one_smul]
  conv_lhs => rw [hspan]
  rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => hterm q

/-- **The coefficient identity (α)(ii)**, in the form used by the Shapiro/cup square: the
evaluation `Φ n` is the trace of the coinduced element `g ↦ ConjHom.evalHom (n 1) ((psiAux U Φ) g)`. -/
theorem evalHom_eq_trace_comp
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (M : Type u) [AddCommGroup M] [DistribMulAction U M]
    (C : Type u) [AddCommGroup C] [DistribMulAction G C]
    (n : Coind G U M) (hn : n ∈ Work.GroupCohomology.invariants G (Coind G U M))
    (Φ : ConjHom (Coind G U M) C) :
    Φ n = trace U C ⟨fun g => ConjHom.evalHom (n 1) ((psiAux U Φ) g), by
      intro g u
      show ConjHom.evalHom (n 1) ((psiAux U Φ) (g * (u : G)))
        = u⁻¹ • ConjHom.evalHom (n 1) ((psiAux U Φ) g)
      rw [Coind.coe_mul]
      exact evalHom_smul (n 1) (val_one_mem_invariants U n hn) u⁻¹ ((psiAux U Φ) g)⟩ := by
  rw [trace_eq_out_sum, evalHom_eq_out_sum U M C n hn Φ]
  exact Finset.sum_congr rfl fun q _ => by
    show Quotient.out q • ((psiAux U Φ) (Quotient.out q)) (n 1)
      = Quotient.out q • ((psiAux U Φ) (Quotient.out q)) (n 1)
    rfl

/-! ## Naturality of Shapiro's isomorphism in the coefficients -/

/-- Naturality of `phiH2` (Shapiro in degree `2`) in the coefficients: `phiH2` commutes with
`mapH2` of a coefficient map and of the induced map on the coinduced modules (a pointwise
computation, since `phiC` evaluates at `1`). -/
theorem phiH2_mapH2_coindMap {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {M M' : Type u} [AddCommGroup M] [DistribMulAction U M] [AddCommGroup M']
    [DistribMulAction U M'] (θ : M →+ M')
    (hθ : Work.GroupCohomology.IsEquivariant U θ)
    (z : Work.AbsoluteKummer.H2 G (Coind G U M)) :
    phiH2 U M' hUo (Work.AbsoluteKummer.mapH2 (CoindMap U θ hθ)
        (isEquivariant_coindMap U θ hθ) z)
      = Work.AbsoluteKummer.mapH2 θ hθ (phiH2 U M hUo z) := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G (Coind G U M)).comap
      (Work.AbsoluteKummer.Z2 G (Coind G U M)).subtype) z
  have hc' : Work.AbsoluteKummer.H2π G (Coind G U M) c = z := hc
  rw [← hc', Work.AbsoluteKummer.mapH2_H2π, phiH2_mk, phiH2_mk, Work.AbsoluteKummer.mapH2_H2π]
  congr 1

/-- **Naturality of Shapiro's isomorphism in the coefficients**, in the `symm` direction (the form
needed by the Shapiro/cup square `(α)`). -/
theorem mapH2_coindMap_shapiroEquiv_symm {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex]
    [Fintype (G ⧸ U)] {M M' : Type u} [AddCommGroup M] [DistribMulAction U M]
    [AddCommGroup M'] [DistribMulAction U M'] (θ : M →+ M')
    (hθ : Work.GroupCohomology.IsEquivariant U θ) :
    (Work.AbsoluteKummer.mapH2 (CoindMap U θ hθ) (isEquivariant_coindMap U θ hθ)).comp
        (shapiroEquiv U hUo (M := M)).symm.toAddMonoidHom
      = (shapiroEquiv U hUo (M := M')).symm.toAddMonoidHom.comp
        (Work.AbsoluteKummer.mapH2 θ hθ) := by
  apply AddMonoidHom.ext
  intro y
  simp only [AddMonoidHom.comp_apply]
  have h := phiH2_mapH2_coindMap U hUo θ hθ ((shapiroEquiv U hUo (M := M)).symm y)
  have h2 : phiH2 U M hUo ((shapiroEquiv U hUo (M := M)).symm y) = y := by
    show shapiroEquiv U hUo (M := M) ((shapiroEquiv U hUo (M := M)).symm y) = y
    exact AddEquiv.apply_symm_apply _ y
  rw [h2] at h
  rw [← h]
  exact (AddEquiv.symm_apply_apply (shapiroEquiv U hUo (M := M'))
    (Work.AbsoluteKummer.mapH2 (CoindMap U θ hθ) (isEquivariant_coindMap U θ hθ)
      ((shapiroEquiv U hUo (M := M)).symm y))).symm


/-! ## The Shapiro/cup square (α) -/

/-- `mapH2` does not depend on the chosen equivariance witness. -/
theorem mapH2_congr_ev {G : Type u} [TopologicalSpace G] [Group G]
    {M : Type u} [AddCommGroup M] [DistribMulAction G M]
    {N : Type u} [AddCommGroup N] [DistribMulAction G N]
    (φ : M →+ N) (h h' : Work.GroupCohomology.IsEquivariant G φ) :
    Work.AbsoluteKummer.mapH2 φ h = Work.AbsoluteKummer.mapH2 φ h' := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) z
  have hc' : Work.AbsoluteKummer.H2π G M c = z := hc
  simp only [← hc', Work.AbsoluteKummer.mapH2_H2π]

/-- The coefficient identity in `AddMonoidHom` form: evaluation at an invariant element `n` of the
coinduced module is the composite of the trace, `CoindMap` of `evalHom (n 1)` and the Frobenius
equivalence. -/
theorem evalHom_eq_trace_comp_frobenius {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (M : Type u) [AddCommGroup M] [DistribMulAction U M]
    (C : Type u) [AddCommGroup C] [DistribMulAction G C]
    (n : Coind G U M) (hn : n ∈ Work.GroupCohomology.invariants G (Coind G U M)) :
    ConjHom.evalHom (C := C) n
      = (trace U C).comp ((CoindMap U (ConjHom.evalHom (C := C) (n 1))
            (evalHom_smul (C := C) (n 1) (val_one_mem_invariants U n hn))).comp
          (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom) := by
  apply AddMonoidHom.ext
  intro Φ₀
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ConjHom.evalHom_apply,
    frobeniusEquiv_toAddMonoidHom_apply]
  exact evalHom_eq_trace_comp U M C n hn Φ₀

/-- **The Shapiro/cup square (α)** of the base case of the `α²`-dévissage: under the Shapiro
identification `H²(G, Hom(Coind^G_U M, C)) ≃ H²(U, Hom(M,C))` (Frobenius plus Shapiro) and the
degree-`0` Shapiro identification `(Coind^G_U M)^G ≅ M^U`, the `α²`-pairing of the coinduced
module over `G` is the `cor`-image of the `α²`-pairing of `M` over `U`. -/
theorem alphaTwo_coind_eq_cor {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex]
    [Fintype (G ⧸ U)] {M : Type u} [AddCommGroup M] [DistribMulAction U M]
    {C : Type u} [AddCommGroup C] [DistribMulAction G C]
    (x : Work.AbsoluteKummer.H2 G (ConjHom (Coind G U M) C))
    (n : ↥(Work.GroupCohomology.invariants G (Coind G U M))) :
    alphaTwo (G := G) (N := Coind G U M) (C := C) x n
      = corH2 U hUo C (alphaTwo (G := U) (N := M) (C := C)
          (shapiroEquiv U hUo (M := ConjHom M C)
            (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
              (isEquivariant_frobeniusEquiv (M := M) (C := C) U) x))
          (shapiroH0AddEquiv U n)) := by
  have hθ : Work.GroupCohomology.IsEquivariant U (ConjHom.evalHom (C := C) (n.1 1)) :=
    evalHom_smul (C := C) (n.1 1) (val_one_mem_invariants U n.1 n.2)
  have htr : Work.GroupCohomology.IsEquivariant G (trace U C) := isEquivariant_trace U C
  have hcm : Work.GroupCohomology.IsEquivariant G
      (CoindMap U (ConjHom.evalHom (C := C) (n.1 1)) hθ) :=
    isEquivariant_coindMap U _ hθ
  have hfe : Work.GroupCohomology.IsEquivariant G
      (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom :=
    isEquivariant_frobeniusEquiv (M := M) (C := C) U
  have hcanon : alphaTwo (G := G) (N := Coind G U M) (C := C) x n
      = Work.AbsoluteKummer.mapH2
          ((trace U C).comp ((CoindMap U (ConjHom.evalHom (C := C) (n.1 1)) hθ).comp
            (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom))
          (Work.GroupCohomology.IsEquivariant.comp htr
            (Work.GroupCohomology.IsEquivariant.comp hcm hfe)) x := by
    rw [alphaTwo_evalHom]
    exact congrArg (fun f => f x) (Work.SSGRoute.PT.mapH2_congr_coeff
      (hφ := evalHom_smul (C := C) (n : Coind G U M) n.2)
      (hψ := Work.GroupCohomology.IsEquivariant.comp htr
        (Work.GroupCohomology.IsEquivariant.comp hcm hfe))
      (evalHom_eq_trace_comp_frobenius U M C n.1 n.2))
  rw [hcanon, corH2_apply, alphaTwo_evalHom]
  -- align the coefficient map `evalHom (shapiroH0AddEquiv U n)` with `evalHom (n 1)`
  rw [show Work.AbsoluteKummer.mapH2 (ConjHom.evalHom (C := C)
        ((shapiroH0AddEquiv U n : ↥(Work.GroupCohomology.invariants U M)) : M))
        (evalHom_smul (C := C)
          ((shapiroH0AddEquiv U n : ↥(Work.GroupCohomology.invariants U M)) : M)
          (shapiroH0AddEquiv U n).2)
      = Work.AbsoluteKummer.mapH2 (ConjHom.evalHom (C := C) (n.1 1)) hθ from
      Work.SSGRoute.PT.mapH2_congr_coeff _ _ rfl]
  -- remove the Shapiro pair via naturality
  rw [show (shapiroEquiv U hUo (M := C)).symm
        (Work.AbsoluteKummer.mapH2 (ConjHom.evalHom (C := C) (n.1 1)) hθ
          (shapiroEquiv U hUo (M := ConjHom M C)
            (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
              hfe x)))
      = Work.AbsoluteKummer.mapH2 (CoindMap U (ConjHom.evalHom (C := C) (n.1 1)) hθ) hcm
          (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
            hfe x) from
      (DFunLike.congr_fun (mapH2_coindMap_shapiroEquiv_symm U hUo
        (θ := ConjHom.evalHom (C := C) (n.1 1)) hθ (M := ConjHom M C) (M' := C))
        (shapiroEquiv U hUo (M := ConjHom M C)
          (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
            hfe x))).symm.trans (by
          show Work.AbsoluteKummer.mapH2 (CoindMap U (ConjHom.evalHom (C := C) (n.1 1)) hθ) hcm
              ((shapiroEquiv U hUo (M := ConjHom M C)).symm
                (shapiroEquiv U hUo (M := ConjHom M C)
                  (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
                    hfe x)))
            = Work.AbsoluteKummer.mapH2 (CoindMap U (ConjHom.evalHom (C := C) (n.1 1)) hθ) hcm
                (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
                  hfe x)
          rw [AddEquiv.symm_apply_apply])]
  -- combine the two `mapH2`s into one
  rw [← mapH2_comp (φ := CoindMap U (ConjHom.evalHom (C := C) (n.1 1)) hθ) (ψ := trace U C)
    hcm htr (Work.GroupCohomology.IsEquivariant.comp htr hcm)
    (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom hfe x)]
  rw [← mapH2_comp (φ := (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom)
    (ψ := (trace U C).comp (CoindMap U (ConjHom.evalHom (C := C) (n.1 1)) hθ)) hfe
    (Work.GroupCohomology.IsEquivariant.comp htr hcm)
    (Work.GroupCohomology.IsEquivariant.comp
      (Work.GroupCohomology.IsEquivariant.comp htr hcm) hfe) x]
  exact (congrArg (fun f => f x) (mapH2_congr_ev
    ((trace U C).comp ((CoindMap U (ConjHom.evalHom (C := C) (n.1 1)) hθ).comp
      (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom)) _ _)).trans rfl

end

end Work.SSGRoute.PT
