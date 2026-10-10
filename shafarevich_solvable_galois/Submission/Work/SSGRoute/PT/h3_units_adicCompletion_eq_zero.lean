import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.Work.SSGRoute.Nakayama.degrees
import Submission.Work.SSGRoute.Nakayama.exists_level_of_locallyConstant_isGalois
import Submission.Work.SSGRoute.PT.isSolvable_algEquiv_of_finiteDimensional
import Submission.Work.SSGRoute.PTCore.H2_level_defs
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H³(G_F, F̄ˣ) = 0` for a `p`-adic field `F`

For `F = Q.adicCompletion K` the completion of a number field at a finite prime, the third
continuous cohomology of the absolute Galois group `G_F` with coefficients in the units `F̄ˣ` of
an algebraic closure vanishes.

The proof reduces to the finite Galois levels:  a locally constant `3`-cocycle `c` with values in
`F̄ˣ` becomes invariant under `Gal(F̄/L)` for some finite Galois `L/F` and takes values in `Lˣ`, so
it descends to a `3`-cocycle of the finite group `Gal(L/F)` with values in `Lˣ`;  and for a finite
Galois extension of a local field the units are a class formation with fundamental class, so
`H³(Gal(L/F), Lˣ) = Ĥ¹(Gal(L/F), ℤ) = 0` by Tate–Nakayama.  Lifting the resulting coboundary back
to `G_F` gives a locally constant `2`-cochain whose `d²` is `c`.
-/

open CategoryTheory
open groupCohomology
open scoped Topology
open Filter

namespace Work.SSGRoute.PT

noncomputable section

set_option linter.style.haveILetI false

/-! ## The `Gal(L/F)`-action on the units of a finite level -/

/-- The `DistribMulAction` of `Gal(L/F)` on the units of a finite Galois level `L`, transported
from the representation `LevelRep L`. -/
instance instDistribMulActionUnitsL {F : Type} [Field F]
    (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    DistribMulAction (PTCore.LevelGal L) (PTCore.UnitsL L) where
  smul γ x := (PTCore.LevelRep L).ρ γ x
  one_smul x := by show (PTCore.LevelRep L).ρ 1 x = x; simp
  mul_smul γ δ x := by
    show (PTCore.LevelRep L).ρ (γ * δ) x = (PTCore.LevelRep L).ρ γ ((PTCore.LevelRep L).ρ δ x)
    simp
  smul_zero γ := by show (PTCore.LevelRep L).ρ γ 0 = 0; simp
  smul_add γ x y := by
    show (PTCore.LevelRep L).ρ γ (x + y) = (PTCore.LevelRep L).ρ γ x + (PTCore.LevelRep L).ρ γ y
    simp

/-- The action of `Gal(L/F)` on the units of a level, unfolded. -/
theorem instDistribMulActionUnitsL_apply {F : Type} [Field F]
    (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (γ : PTCore.LevelGal L)
    (x : PTCore.UnitsL L) : γ • x = (PTCore.LevelRep L).ρ γ x := rfl

/-! ## Auxiliary inputs -/

/-- **Compactness**: a locally constant function on `G_k × G_k × G_k` is right-invariant under the
fixing subgroup of a single finite Galois level. -/
theorem exists_finiteGalois_le_ker_triple {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)]
    {M : Type*}
    {f : Work.AbsoluteKummer.G k × Work.AbsoluteKummer.G k × Work.AbsoluteKummer.G k → M}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ L : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      ∀ p : Work.AbsoluteKummer.G k × Work.AbsoluteKummer.G k × Work.AbsoluteKummer.G k,
        p.1 ∈ L.fixingSubgroup → p.2.1 ∈ L.fixingSubgroup → p.2.2 ∈ L.fixingSubgroup →
          f p = f (1, 1, 1) := by
  obtain ⟨U, hUo, h1U, hconst⟩ := hf (1, 1, 1)
  have hUmem : U ∈ 𝓝 ((1, 1, 1) :
      Work.AbsoluteKummer.G k × Work.AbsoluteKummer.G k × Work.AbsoluteKummer.G k) :=
    hUo.mem_nhds h1U
  rw [nhds_prod_eq] at hUmem
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := Filter.mem_prod_iff.mp hUmem
  rw [nhds_prod_eq] at hU₂
  obtain ⟨U₂', hU₂', U₃', hU₃', hsub₂⟩ := Filter.mem_prod_iff.mp hU₂
  have hmem : U₁ ∩ U₂' ∩ U₃' ∈ 𝓝 (1 : Work.AbsoluteKummer.G k) :=
    Filter.inter_mem (Filter.inter_mem hU₁ hU₂') hU₃'
  obtain ⟨L, hL⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (k := k)
      (K := AlgebraicClosure k) (U₁ ∩ U₂' ∩ U₃')).mp hmem
  exact ⟨L, fun p hp1 hp2 hp3 =>
    hconst p (hsub ⟨(hL hp1).1.1, hsub₂ ⟨(hL hp2).1.2, (hL hp3).2⟩⟩)⟩

/-- Every locally constant `3`-cochain with values in the units of an algebraic closure becomes
invariant under a finite Galois level and takes values in the units of that level. -/
theorem exists_level_of_locallyConstant_isGalois_three
    (k : Type*) [Field k] [IsGalois k (AlgebraicClosure k)]
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) × (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hd : Work.AbsoluteKummer.IsLocallyConstant d) :
    ∃ (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)),
      (∀ (g h i u v w : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k),
        u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
        v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
        w ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
        d (g * u, h * v, i * w) = d (g, h, i)) ∧
      (∀ g h i, ∃ x : (L : IntermediateField k (AlgebraicClosure k))ˣ,
        Units.map (algebraMap (L : IntermediateField k (AlgebraicClosure k))
          (AlgebraicClosure k)).toMonoidHom x = Additive.toMul (d (g, h, i))) := by
  have hvalfin : (Set.range d).Finite := Work.AbsoluteKummer.finite_image_of_isLocallyConstant hd
  let S : Set (AlgebraicClosure k) :=
    (fun u : (AlgebraicClosure k)ˣ => (u : AlgebraicClosure k)) ''
      (Additive.toMul '' (Set.range d))
  have hSfin : S.Finite := (hvalfin.image Additive.toMul).image _
  haveI : Finite S := hSfin.to_subtype
  let Lv : FiniteGaloisIntermediateField k (AlgebraicClosure k) :=
    FiniteGaloisIntermediateField.adjoin k S
  have hval : ∀ p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) × (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k),
      ((Additive.toMul (d p) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ∈
        (Lv : IntermediateField k (AlgebraicClosure k)) := by
    intro p
    have hxS : ((Additive.toMul (d p) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ∈ S :=
      ⟨Additive.toMul (d p), ⟨d p, ⟨p, rfl⟩, rfl⟩, rfl⟩
    exact FiniteGaloisIntermediateField.subset_adjoin k S hxS
  have key : ∀ x : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) × (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k),
      ∃ L : FiniteGaloisIntermediateField k (AlgebraicClosure k),
        ∀ u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup,
          ∀ v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup,
          ∀ w ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup,
          d (x.1 * u, x.2.1 * v, x.2.2 * w) = d x := by
    intro x
    have hcont : Continuous fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) × (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) =>
        (x.1 * p.1, x.2.1 * p.2.1, x.2.2 * p.2.2) := by fun_prop
    have hloc := Work.SSGRoute.Nakayama.isLocallyConstant_comp_continuous_aux hd hcont
    obtain ⟨L, hL⟩ := exists_finiteGalois_le_ker_triple hloc
    exact ⟨L, fun u hu v hv w hw => by
      have := hL (u, v, w) hu hv hw
      simpa [Function.comp_apply, mul_one] using this⟩
  choose Lf hLf using key
  let U : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) × (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      Set ((AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) × (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) :=
    fun x =>
      (Homeomorph.mulLeft x.1 '' ((Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :
        Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k))) ×ˢ
      ((Homeomorph.mulLeft x.2.1 '' ((Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :
        Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k))) ×ˢ
       (Homeomorph.mulLeft x.2.2 '' ((Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :
        Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k))))
  have hUopen : ∀ x, IsOpen (U x) := by
    intro x
    exact ((Homeomorph.mulLeft x.1).isOpenMap _
        (IntermediateField.fixingSubgroup_isOpen
          (Lf x : IntermediateField k (AlgebraicClosure k)))).prod
      (((Homeomorph.mulLeft x.2.1).isOpenMap _
        (IntermediateField.fixingSubgroup_isOpen
          (Lf x : IntermediateField k (AlgebraicClosure k)))).prod
       ((Homeomorph.mulLeft x.2.2).isOpenMap _
        (IntermediateField.fixingSubgroup_isOpen
          (Lf x : IntermediateField k (AlgebraicClosure k)))))
  have hUcover : (Set.univ : Set ((AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) × (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)))
      ⊆ ⋃ x, U x := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_, ?_, ?_⟩
    · exact ⟨1, (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup.one_mem, by simp⟩
    · exact ⟨1, (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup.one_mem, by simp⟩
    · exact ⟨1, (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup.one_mem, by simp⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcover
  let L₀ : FiniteGaloisIntermediateField k (AlgebraicClosure k) := t.sup Lf
  have hinv₀ : ∀ g h i u v w : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (L₀ : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (L₀ : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      w ∈ (L₀ : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u, h * v, i * w) = d (g, h, i) := by
    intro g h i u v w hu hv hw
    have hmem : (g, h, i) ∈ ⋃ x ∈ t, U x := ht (Set.mem_univ (g, h, i))
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨x, hxt, hxU⟩ := hmem
    obtain ⟨u₀, hu₀, hgu⟩ := hxU.1
    obtain ⟨v₀, hv₀, hhv⟩ := hxU.2.1
    obtain ⟨w₀, hw₀, hiw⟩ := hxU.2.2
    have hle : Lf x ≤ L₀ := Finset.le_sup hxt
    have hfix : (L₀ : IntermediateField k (AlgebraicClosure k)).fixingSubgroup ≤
        (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone hle
    have hu' : u₀ * u ∈ (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :=
      Subgroup.mul_mem _ hu₀ (hfix hu)
    have hv' : v₀ * v ∈ (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :=
      Subgroup.mul_mem _ hv₀ (hfix hv)
    have hw' : w₀ * w ∈ (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :=
      Subgroup.mul_mem _ hw₀ (hfix hw)
    have h1 : d (x.1 * (u₀ * u), x.2.1 * (v₀ * v), x.2.2 * (w₀ * w)) = d x :=
      hLf x (u₀ * u) hu' (v₀ * v) hv' (w₀ * w) hw'
    have h2 : d (x.1 * u₀, x.2.1 * v₀, x.2.2 * w₀) = d x :=
      hLf x u₀ hu₀ v₀ hv₀ w₀ hw₀
    have hgu' : g = x.1 * u₀ := by simpa using hgu.symm
    have hhv' : h = x.2.1 * v₀ := by simpa using hhv.symm
    have hiw' : i = x.2.2 * w₀ := by simpa using hiw.symm
    rw [hgu', hhv', hiw']
    calc d ((x.1 * u₀) * u, (x.2.1 * v₀) * v, (x.2.2 * w₀) * w)
        = d (x.1 * (u₀ * u), x.2.1 * (v₀ * v), x.2.2 * (w₀ * w)) := by
          rw [mul_assoc, mul_assoc, mul_assoc]
      _ = d x := h1
      _ = d (x.1 * u₀, x.2.1 * v₀, x.2.2 * w₀) := h2.symm
  refine ⟨L₀ ⊔ Lv, ?_, ?_⟩
  · intro g h i u v w hu hv hw
    exact hinv₀ g h i u v w
      (IntermediateField.fixingSubgroup_antitone (le_sup_left : L₀ ≤ L₀ ⊔ Lv) hu)
      (IntermediateField.fixingSubgroup_antitone (le_sup_left : L₀ ≤ L₀ ⊔ Lv) hv)
      (IntermediateField.fixingSubgroup_antitone (le_sup_left : L₀ ≤ L₀ ⊔ Lv) hw)
  · intro g h i
    have hle : (Lv : IntermediateField k (AlgebraicClosure k)) ≤
        ((L₀ ⊔ Lv : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
          IntermediateField k (AlgebraicClosure k)) := by
      rw [← FiniteGaloisIntermediateField.le_iff]
      exact le_sup_right
    have hmem : ((Additive.toMul (d (g, h, i)) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ∈
        ((L₀ ⊔ Lv : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
          IntermediateField k (AlgebraicClosure k)) :=
      hle (hval (g, h, i))
    refine ⟨Units.mk0 ⟨_, hmem⟩ ?_, ?_⟩
    · intro hzero
      have h2 : ((Additive.toMul (d (g, h, i)) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) = 0 := by
        have := congrArg
          (fun z : ((L₀ ⊔ Lv : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
            IntermediateField k (AlgebraicClosure k)) => ((z : AlgebraicClosure k))) hzero
        simpa using this
      exact Units.ne_zero (d (g, h, i)) h2
    · ext
      simp [Units.coe_map]

/-- `H³(Gal(E/F), Eˣ) = 0` for a finite Galois extension `E` of a `p`-adic field. -/
theorem subsingleton_groupCohomology_three_adicCompletion
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E] :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 3) := by
  classical
  haveI hsolv : Group.IsSolvable (E ≃ₐ[Q.adicCompletion K] E) :=
    isSolvable_algEquiv_of_finiteDimensional (K := K) Q
  obtain ⟨h1, h2, α, hα⟩ :=
    localCohomologicalFieldAxiom_units (K := K) Q (F := Q.adicCompletion K) (E := E)
  obtain ⟨e⟩ := Work.SSGRoute.Nakayama.tateNakayama_int
    (C := Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) h1 h2 α hα 1
  have htriv : Subsingleton
      (tateCohomology (Rep.trivial ℤ (E ≃ₐ[Q.adicCompletion K] E) ℤ) 1) := by
    refine ⟨fun a b => ?_⟩
    apply (TateCohomology.isoGroupCohomology (R := ℤ)
      (G := E ≃ₐ[Q.adicCompletion K] E) 1).app (Rep.trivial ℤ _ ℤ) |>.toLinearEquiv.toEquiv.injective
    exact (NU.subsingleton_groupCohomology_trivial_int_one (G := E ≃ₐ[Q.adicCompletion K] E)).elim _ _
  have hcast : (1 : ℤ) + 2 = 3 := by norm_num
  have hC3 : Subsingleton
      (tateCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 3) := by
    rw [← hcast]
    refine ⟨fun a b => ?_⟩
    exact e.symm.injective (htriv.elim _ _)
  refine ⟨fun a b => ?_⟩
  apply (TateCohomology.isoGroupCohomology (R := ℤ)
    (G := E ≃ₐ[Q.adicCompletion K] E) 3).app
      (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) |>.toLinearEquiv.toEquiv.symm.injective
  exact hC3.elim _ _

/-- The degree-`3` cocycle identity, in a form that does not mention the topology. -/
theorem d3_apply' {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [DistribMulAction G A]
    (c : G × G × G → A) (g h k l : G) :
    Work.SSGRoute.d3 c (g, h, k, l)
      = g • c (h, k, l) - c (g * h, k, l) + c (g, h * k, l) - c (g, h, k * l)
        + c (g, h, k) := rfl

/-! ## The inhomogeneous differentials in tuple coordinates -/

section Differential

set_option backward.isDefEq.respectTransparency false
attribute [local instance 10000] Rep.hV2 Rep.hV1

variable {Γ : Type} [Group Γ]

theorem contractNth_four_zero {α : Type*} (op : α → α → α) (a b c d : α) :
    Fin.contractNth (0 : Fin 4) op ![a, b, c, d] = ![op a b, c, d] := by
  funext k; fin_cases k <;> simp [Fin.contractNth]

theorem contractNth_four_one {α : Type*} (op : α → α → α) (a b c d : α) :
    Fin.contractNth (1 : Fin 4) op ![a, b, c, d] = ![a, op b c, d] := by
  funext k; fin_cases k <;> simp [Fin.contractNth]

theorem contractNth_four_two {α : Type*} (op : α → α → α) (a b c d : α) :
    Fin.contractNth (2 : Fin 4) op ![a, b, c, d] = ![a, b, op c d] := by
  funext k; fin_cases k <;> simp [Fin.contractNth]

theorem contractNth_four_three {α : Type*} (op : α → α → α) (a b c d : α) :
    Fin.contractNth (3 : Fin 4) op ![a, b, c, d] = ![a, b, c] := by
  funext k; fin_cases k <;> simp [Fin.contractNth]

theorem contractNth_three_zero {α : Type*} (op : α → α → α) (a b c : α) :
    Fin.contractNth (0 : Fin 3) op ![a, b, c] = ![op a b, c] := by
  funext k; fin_cases k <;> simp [Fin.contractNth]

theorem contractNth_three_one {α : Type*} (op : α → α → α) (a b c : α) :
    Fin.contractNth (1 : Fin 3) op ![a, b, c] = ![a, op b c] := by
  funext k; fin_cases k <;> simp [Fin.contractNth]

theorem contractNth_three_two {α : Type*} (op : α → α → α) (a b c : α) :
    Fin.contractNth (2 : Fin 3) op ![a, b, c] = ![a, b] := by
  funext k; fin_cases k <;> simp [Fin.contractNth]

theorem tuple_four {Γ : Type} (g : Fin 4 → Γ) : g = ![g 0, g 1, g 2, g 3] := by
  funext i; fin_cases i <;> rfl

/-- The degree-`3` inhomogeneous differential on a `Fin 3`-tuple. -/
theorem d_three_apply (A : Rep ℤ Γ) (f : (Fin 3 → Γ) → A.V) (a b c d : Γ) :
    (inhomogeneousCochains.d A 3 f) ![a, b, c, d]
      = A.ρ a (f ![b, c, d]) - f ![a * b, c, d] + f ![a, b * c, d]
        - f ![a, b, c * d] + f ![a, b, c] := by
  simp only [inhomogeneousCochains.d, ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fin.sum_univ_four]
  rw [contractNth_four_zero, contractNth_four_one, contractNth_four_two, contractNth_four_three]
  have hhead : (![a, b, c, d] : Fin 4 → Γ) 0 = a := rfl
  have htail : (fun i : Fin 3 => (![a, b, c, d] : Fin 4 → Γ) i.succ) = ![b, c, d] := by
    funext i; fin_cases i <;> rfl
  rw [hhead, htail]
  rw [show (((0 : Fin 4) : ℕ) + 1) = 1 from by decide,
      show (((1 : Fin 4) : ℕ) + 1) = 2 from by decide,
      show (((2 : Fin 4) : ℕ) + 1) = 3 from by decide,
      show (((3 : Fin 4) : ℕ) + 1) = 4 from by decide]
  norm_num
  simp only [one_smul, neg_smul, sub_eq_add_neg]
  ac_rfl

/-- The degree-`2` inhomogeneous differential on a `Fin 2`-tuple. -/
theorem d_two_apply (A : Rep ℤ Γ) (f : (Fin 2 → Γ) → A.V) (a b c : Γ) :
    (inhomogeneousCochains.d A 2 f) ![a, b, c]
      = A.ρ a (f ![b, c]) - f ![a * b, c] + f ![a, b * c] - f ![a, b] := by
  simp only [inhomogeneousCochains.d, ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fin.sum_univ_three]
  rw [contractNth_three_zero, contractNth_three_one, contractNth_three_two]
  have hhead : (![a, b, c] : Fin 3 → Γ) 0 = a := rfl
  have htail : (fun i : Fin 2 => (![a, b, c] : Fin 3 → Γ) i.succ) = ![b, c] := by
    funext i; fin_cases i <;> rfl
  rw [hhead, htail]
  rw [show (((0 : Fin 3) : ℕ) + 1) = 1 from by decide,
      show (((1 : Fin 3) : ℕ) + 1) = 2 from by decide,
      show (((2 : Fin 3) : ℕ) + 1) = 3 from by decide]
  norm_num
  simp only [one_smul, neg_smul, sub_eq_add_neg]
  ac_rfl

end Differential

/-- If the third group cohomology of a finite group vanishes, then every explicit `3`-cocycle in
the workspace's cochain model is an explicit `2`-coboundary. -/
theorem exists_d2_eq_of_subsingleton_groupCohomology_three
    {Γ : Type} [Group Γ] [Fintype Γ] {M : Type} [AddCommGroup M] [DistribMulAction Γ M]
    (A : Rep ℤ Γ) (φ : A.V ≃+ M) (hφ : ∀ (g : Γ) (v : A.V), φ (A.ρ g v) = g • φ v)
    (h : Subsingleton (groupCohomology A 3)) :
    ∀ c : Γ × Γ × Γ → M, Work.SSGRoute.d3 c = 0 →
      ∃ b : Γ × Γ → M, Work.GroupCohomology.d2 Γ M b = c := by
  intro c hc
  classical
  let z : (Fin 3 → Γ) → A.V := fun f => φ.symm (c (f 0, f 1, f 2))
  have hz : (inhomogeneousCochains A).d 3 4 z = 0 := by
    funext g
    rw [show g = ![g 0, g 1, g 2, g 3] from tuple_four g]
    change ((inhomogeneousCochains A).d 3 4) z ![g 0, g 1, g 2, g 3] = (0 : A.V)
    rw [inhomogeneousCochains.d_def, d_three_apply]
    apply φ.injective
    rw [map_zero]
    simp only [map_add, map_sub, hφ, z, AddEquiv.apply_symm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have hcc := congrFun hc (g 0, g 1, g 2, g 3)
    rw [d3_apply'] at hcc
    exact hcc
  have hexact : (inhomogeneousCochains A).ExactAt 3 := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (ModuleCat.isZero_iff_subsingleton (R := ℤ)).mpr h
  obtain ⟨y, hy⟩ : ∃ y : (inhomogeneousCochains A).X 2,
      (inhomogeneousCochains A).d 2 3 y = z := by
    have hex := hexact
    rw [HomologicalComplex.exactAt_iff' (inhomogeneousCochains A) 2 3 4 (by simp) (by simp)] at hex
    rw [ShortComplex.moduleCat_exact_iff] at hex
    exact hex z hz
  let b : Γ × Γ → M := fun p => φ (y ![p.1, p.2])
  refine ⟨b, ?_⟩
  funext p
  obtain ⟨a₀, b₀, c₀⟩ := p
  rw [Work.GroupCohomology.d2_apply]
  have hconv : a₀ • b (b₀, c₀) - b (a₀ * b₀, c₀) + b (a₀, b₀ * c₀) - b (a₀, b₀)
      = φ ((inhomogeneousCochains A).d 2 3 y ![a₀, b₀, c₀]) := by
    rw [inhomogeneousCochains.d_def, d_two_apply]
    simp only [b]
    rw [← hφ a₀ (y ![b₀, c₀]), ← map_sub, ← map_add, ← map_sub]
  rw [hconv, hy]
  simp only [z, AddEquiv.apply_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply]

end

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

noncomputable section

set_option linter.style.haveILetI false

/-- **Reduction of `H³(G_F, F̄ˣ) = 0` to the finite Galois levels.**  If the third cohomology of
`Gal(L/F)` with coefficients in `Lˣ` vanishes for every finite Galois level `L/F`, then the third
continuous cohomology of `G_F` with coefficients in `F̄ˣ` vanishes. -/
theorem subsingleton_H3_unitsK_of_level
    (F : Type) [Field F] [IsGalois F (AlgebraicClosure F)]
    (h3 : ∀ (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)),
      Subsingleton (groupCohomology (PTCore.LevelRep L) 3)) :
    Subsingleton (Work.SSGRoute.H3 (M := PTCore.UnitsK F)
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) := by
  classical
  have hmem : ∀ c : ↥(Work.SSGRoute.Z3 (M := PTCore.UnitsK F)
        (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)),
      ((c : (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ×
        (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ×
        (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) → PTCore.UnitsK F))
        ∈ Work.SSGRoute.B3 (M := PTCore.UnitsK F)
            (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) := by
    intro c
    obtain ⟨hcoc, hlc⟩ := (Work.SSGRoute.mem_Z3_iff
      (G := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (M := PTCore.UnitsK F)).mp c.2
    obtain ⟨L, hinv, hval⟩ := exists_level_of_locallyConstant_isGalois_three F
      (c : (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ×
        (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ×
        (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) → PTCore.UnitsK F) hlc
    -- a set-theoretic section of the restriction
    set sec : PTCore.LevelGal L → (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
      fun γ => Classical.choose (PTCore.resL_surjective L γ) with hsecdef
    have hsec : ∀ γ, PTCore.resL L (sec γ) = γ :=
      fun γ => Classical.choose_spec (PTCore.resL_surjective L γ)
    -- the descended cocycle
    have hex : ∀ p : PTCore.LevelGal L × PTCore.LevelGal L × PTCore.LevelGal L,
        ∃ x : PTCore.UnitsL L,
          PTCore.inclL L x = (c : _ → PTCore.UnitsK F) (sec p.1, sec p.2.1, sec p.2.2) := by
      intro p
      obtain ⟨x, hx⟩ := hval (sec p.1) (sec p.2.1) (sec p.2.2)
      exact ⟨Additive.ofMul x, by rw [PTCore.inclL_ofMul, hx, ofMul_toMul]⟩
    set cL : PTCore.LevelGal L × PTCore.LevelGal L × PTCore.LevelGal L → PTCore.UnitsL L :=
      fun p => Classical.choose (hex p) with hcLdef
    have hcL : ∀ p, PTCore.inclL L (cL p) =
        (c : _ → PTCore.UnitsK F) (sec p.1, sec p.2.1, sec p.2.2) :=
      fun p => Classical.choose_spec (hex p)
    -- the level `3`-cocycle condition
    have hrel : ∀ γ δ : PTCore.LevelGal L,
        (sec (γ * δ))⁻¹ * (sec γ * sec δ) ∈ PTCore.lvlFix L := by
      intro γ δ
      rw [← PTCore.mem_ker_resL_iff L]
      rw [map_mul, map_mul, map_inv, hsec γ, hsec δ, hsec (γ * δ)]
      group
    have hinv1 : ∀ (g h i u : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F),
        u ∈ PTCore.lvlFix L → (c : _ → PTCore.UnitsK F) (g * u, h, i) =
          (c : _ → PTCore.UnitsK F) (g, h, i) := by
      intro g h i u hu
      have := hinv g h i u 1 1 hu (Subgroup.one_mem _) (Subgroup.one_mem _)
      simpa using this
    have hinv2 : ∀ (g h i u : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F),
        u ∈ PTCore.lvlFix L → (c : _ → PTCore.UnitsK F) (g, h * u, i) =
          (c : _ → PTCore.UnitsK F) (g, h, i) := by
      intro g h i u hu
      have := hinv g h i 1 u 1 (Subgroup.one_mem _) hu (Subgroup.one_mem _)
      simpa using this
    have hinv3 : ∀ (g h i u : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F),
        u ∈ PTCore.lvlFix L → (c : _ → PTCore.UnitsK F) (g, h, i * u) =
          (c : _ → PTCore.UnitsK F) (g, h, i) := by
      intro g h i u hu
      have := hinv g h i 1 1 u (Subgroup.one_mem _) (Subgroup.one_mem _) hu
      simpa using this
    have hcocL : Work.SSGRoute.d3 (G := PTCore.LevelGal L) (A := PTCore.UnitsL L) cL = 0 := by
      funext p
      obtain ⟨γ, δ, ε, ζ⟩ := p
      rw [Work.SSGRoute.d3_apply]
      refine PTCore.inclL_injective L ?_
      simp only [Pi.zero_apply, map_zero]
      have e1 : PTCore.inclL L (γ • cL (δ, ε, ζ))
          = sec γ • (c : _ → PTCore.UnitsK F) (sec δ, sec ε, sec ζ) := by
        rw [show γ • cL (δ, ε, ζ)
          = (PTCore.LevelRep L).ρ (PTCore.resL L (sec γ)) (cL (δ, ε, ζ)) from by rw [hsec γ]; rfl]
        rw [PTCore.inclL_rho, hcL]
      have e2 : PTCore.inclL L (cL (γ * δ, ε, ζ))
          = (c : _ → PTCore.UnitsK F) (sec γ * sec δ, sec ε, sec ζ) := by
        rw [hcL (γ * δ, ε, ζ)]
        have h := hinv1 (sec (γ * δ)) (sec ε) (sec ζ)
          ((sec (γ * δ))⁻¹ * (sec γ * sec δ)) (hrel γ δ)
        rw [show sec (γ * δ) * ((sec (γ * δ))⁻¹ * (sec γ * sec δ)) = sec γ * sec δ from by group] at h
        exact h.symm
      have e3 : PTCore.inclL L (cL (γ, δ * ε, ζ))
          = (c : _ → PTCore.UnitsK F) (sec γ, sec δ * sec ε, sec ζ) := by
        rw [hcL (γ, δ * ε, ζ)]
        have h := hinv2 (sec γ) (sec (δ * ε)) (sec ζ)
          ((sec (δ * ε))⁻¹ * (sec δ * sec ε)) (hrel δ ε)
        rw [show sec (δ * ε) * ((sec (δ * ε))⁻¹ * (sec δ * sec ε)) = sec δ * sec ε from by group] at h
        exact h.symm
      have e4 : PTCore.inclL L (cL (γ, δ, ε * ζ))
          = (c : _ → PTCore.UnitsK F) (sec γ, sec δ, sec ε * sec ζ) := by
        rw [hcL (γ, δ, ε * ζ)]
        have h := hinv3 (sec γ) (sec δ) (sec (ε * ζ))
          ((sec (ε * ζ))⁻¹ * (sec ε * sec ζ)) (hrel ε ζ)
        rw [show sec (ε * ζ) * ((sec (ε * ζ))⁻¹ * (sec ε * sec ζ)) = sec ε * sec ζ from by group] at h
        exact h.symm
      have hkey : PTCore.inclL L (γ • cL (δ, ε, ζ) - cL (γ * δ, ε, ζ) + cL (γ, δ * ε, ζ)
            - cL (γ, δ, ε * ζ) + cL (γ, δ, ε))
          = sec γ • (c : _ → PTCore.UnitsK F) (sec δ, sec ε, sec ζ)
            - (c : _ → PTCore.UnitsK F) (sec γ * sec δ, sec ε, sec ζ)
            + (c : _ → PTCore.UnitsK F) (sec γ, sec δ * sec ε, sec ζ)
            - (c : _ → PTCore.UnitsK F) (sec γ, sec δ, sec ε * sec ζ)
            + (c : _ → PTCore.UnitsK F) (sec γ, sec δ, sec ε) := by
        simp only [map_add, map_sub, e1, e2, e3, e4, hcL (γ, δ, ε)]
      rw [hkey]
      have hcz := congrFun hcoc (sec γ, sec δ, sec ε, sec ζ)
      rw [Work.SSGRoute.d3_apply] at hcz
      exact hcz
    -- the finite-level vanishing
    haveI : Subsingleton (groupCohomology (PTCore.LevelRep L) 3) := h3 L
    obtain ⟨bL, hbL⟩ := exists_d2_eq_of_subsingleton_groupCohomology_three
      (Γ := PTCore.LevelGal L) (M := PTCore.UnitsL L) (A := PTCore.LevelRep L)
      (φ := AddEquiv.refl _) (fun g v => rfl) inferInstance cL hcocL
    -- lift the coboundary back to `G_F`
    refine ⟨fun p => PTCore.inclL L (bL (PTCore.resL L p.1, PTCore.resL L p.2)),
      PTCore.isLocallyConstant_comp_pairResL L (fun q => PTCore.inclL L (bL q)), ?_⟩
    funext p
    obtain ⟨g, h, k⟩ := p
    rw [Work.GroupCohomology.d2_apply]
    have hd2 : (Work.GroupCohomology.d2 (PTCore.LevelGal L) (PTCore.UnitsL L)) bL
        (PTCore.resL L g, PTCore.resL L h, PTCore.resL L k)
        = cL (PTCore.resL L g, PTCore.resL L h, PTCore.resL L k) := congrFun hbL _
    rw [map_mul, map_mul, ← PTCore.inclL_rho L g (bL (PTCore.resL L h, PTCore.resL L k))]
    rw [← map_sub, ← map_add, ← map_sub]
    rw [show (PTCore.LevelRep L).ρ (PTCore.resL L g) (bL (PTCore.resL L h, PTCore.resL L k))
          - bL (PTCore.resL L g * PTCore.resL L h, PTCore.resL L k)
          + bL (PTCore.resL L g, PTCore.resL L h * PTCore.resL L k)
          - bL (PTCore.resL L g, PTCore.resL L h)
        = (Work.GroupCohomology.d2 (PTCore.LevelGal L) (PTCore.UnitsL L)) bL
            (PTCore.resL L g, PTCore.resL L h, PTCore.resL L k) from by
        rw [Work.GroupCohomology.d2_apply, instDistribMulActionUnitsL_apply]]
    rw [hd2, hcL (PTCore.resL L g, PTCore.resL L h, PTCore.resL L k)]
    have hinvg1 : ((sec (PTCore.resL L g))⁻¹ * g) ∈ PTCore.lvlFix L := by
      rw [← PTCore.mem_ker_resL_iff L]
      rw [map_mul, map_inv, hsec (PTCore.resL L g)]
      group
    have hinvg2 : ((sec (PTCore.resL L h))⁻¹ * h) ∈ PTCore.lvlFix L := by
      rw [← PTCore.mem_ker_resL_iff L]
      rw [map_mul, map_inv, hsec (PTCore.resL L h)]
      group
    have hinvg3 : ((sec (PTCore.resL L k))⁻¹ * k) ∈ PTCore.lvlFix L := by
      rw [← PTCore.mem_ker_resL_iff L]
      rw [map_mul, map_inv, hsec (PTCore.resL L k)]
      group
    have hfin := hinv (sec (PTCore.resL L g)) (sec (PTCore.resL L h)) (sec (PTCore.resL L k))
      ((sec (PTCore.resL L g))⁻¹ * g) ((sec (PTCore.resL L h))⁻¹ * h)
      ((sec (PTCore.resL L k))⁻¹ * k) hinvg1 hinvg2 hinvg3
    rw [show sec (PTCore.resL L g) * ((sec (PTCore.resL L g))⁻¹ * g) = g from by group,
      show sec (PTCore.resL L h) * ((sec (PTCore.resL L h))⁻¹ * h) = h from by group,
      show sec (PTCore.resL L k) * ((sec (PTCore.resL L k))⁻¹ * k) = k from by group] at hfin
    exact hfin.symm
  -- conclude
  refine ⟨fun x y => ?_⟩
  have hzero : ∀ x : Work.SSGRoute.H3 (M := PTCore.UnitsK F)
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F), x = 0 := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective
      ((Work.SSGRoute.B3 (M := PTCore.UnitsK F)
        (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)).comap
        (Work.SSGRoute.Z3 (M := PTCore.UnitsK F)
          (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)).subtype) x
    rw [← Work.SSGRoute.H3π_apply (M := PTCore.UnitsK F)
        (G := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) c]
    rw [Work.SSGRoute.H3π_eq_zero_iff]
    exact hmem c
  exact (hzero x).trans (hzero y).symm

end

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

theorem h3_units_adicCompletion_eq_zero
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Subsingleton (Work.SSGRoute.H3 (M := Additive ((AlgebraicClosure (Q.adicCompletion K))ˣ))
      (Work.AbsoluteKummer.G (Q.adicCompletion K))) := by
  exact subsingleton_H3_unitsK_of_level (Q.adicCompletion K)
    (fun L => subsingleton_groupCohomology_three_adicCompletion (K := K) Q (E := ↥L))

end Work.SSGRoute.PT
