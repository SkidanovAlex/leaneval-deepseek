import Mathlib
import Submission.Work.ATOM.ZS.NullSeqMaps
import Submission.Work.ANALYTIC.EA_shift
import Submission.Work.ANALYTIC.whiskerRight_sub_lightCondMod

/-!
# AREA ATOM / `ℤ[S]`: the comparison space for the identity `h₄`

This file sets up the "closed cover" along which the identity `h₄` of REFS/03 §1
(`Work.ATOM.m S ≫ Work.ATOM.G S = Work.ATOM.preShiftP ≫ Work.ATOM.FP S`) is checked.

The source of `h₄` is `P ⊗ P`, which is a quotient of `ℤ[(ℕ∪∞) × (ℕ∪∞)]`.  Both sides are first
pulled back to the "graph" cover `(ℕ∪∞) × T'` of `(ℕ∪∞) × (ℕ∪∞)` (recall
`T' = {(j,a_j)} ∪ {∞} × S ⟶ ℕ∪∞` is surjective), where they become explicit combinations of
`zmap`s:

* `LHS = (zmap ψ₁ - zmap ψ₂) ≫ P_proj` with `ψ₁(k,t) = ψ(k, pr₂ t)`, `ψ₂(k,t) = ψ(k, β t)`;
* `RHS = (zmap φ₁ - zmap φ₂) ≫ P_proj` with `φ₁(k,t) = φ_P(k, tProj t)`,
  `φ₂(k,t) = φ_P(k+1, tProj t)`.

The two sides are then compared on the two closed pieces
* `hFourCA`, where `ψ₁ = ψ₂` and `φ₁ = φ₂` (both sides vanish), and
* `hFourCB`, where `ψ₁ = φ₁` and `ψ₂ = φ₂` (the two sides agree term by term),

which cover `(ℕ∪∞) × T'`: if `t` lies over `∞` or `k = ∞` or `k ≠ n(j)` one is in `hFourCA`, and
for `k = n(j)` one is in `hFourCB`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open OnePoint

noncomputable section

namespace Work.ATOM.ZS

/-! ## Two elementary categorical lemmas -/

/-- The functor `X ⊗ -` is additive on light condensed abelian groups (it is a left adjoint, so
it preserves colimits, hence binary biproducts). -/
theorem hFour_tensorLeft_additive (X : LightCondAb) : (tensorLeft X).Additive := by
  have h : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  have h2 : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X) :=
    h.preservesColimitsOfShape
  have h3 : PreservesBinaryBiproducts (tensorLeft X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Left whiskering is additive: `X ◁ (f - g) = X ◁ f - X ◁ g`. -/
theorem hFour_whiskerLeft_sub (X : LightCondAb) {Y Z : LightCondAb} (f g : Y ⟶ Z) :
    X ◁ (f - g) = X ◁ f - X ◁ g := by
  haveI := hFour_tensorLeft_additive X
  exact Functor.map_sub (tensorLeft X)

/-- The quotient projection `EApp : ℤ[(ℕ∪∞) × (ℕ∪∞)] ⟶ P ⊗ P` is an epimorphism (it is the
composite of the isomorphism `μ⁻¹` with the two cokernel projections
`P_proj ▷ ℤ[ℕ∪∞]` and `P ◁ P_proj`, which are epimorphisms because `tensorRight`/`tensorLeft` are
left adjoints). -/
theorem hFour_epi_EApp : Epi (Work.ATOM.EApp :
    Work.ATOM.zfree Work.ATOM.NS2 ⟶ Work.ATOM.tmul LightCondensed.P LightCondensed.P) := by
  have hP : Epi LightCondensed.P_proj :=
    inferInstanceAs (Epi (cokernel.π LightCondensed.P_map))
  have h1 : Epi (LightCondensed.P_proj ▷ Work.ATOM.zfree LightProfinite.NatUnionInfty) := by
    haveI := hP
    exact Functor.map_epi (MonoidalCategory.tensorRight
      (Work.ATOM.zfree LightProfinite.NatUnionInfty)) LightCondensed.P_proj
  have h2 : Epi (LightCondensed.P ◁ LightCondensed.P_proj) := by
    haveI := hP
    exact Functor.map_epi (MonoidalCategory.tensorLeft LightCondensed.P) LightCondensed.P_proj
  rw [Work.ATOM.EApp]
  exact epi_comp _ _

variable (S : LightProfinite.{0}) [Infinite S]

/-- The covering space `(ℕ∪∞) × T'` on which the identity `h₄` is checked. -/
abbrev hFourW : LightProfinite.{0} := (ℕ∪{∞}) ⊗ T' S

/-- `id × tProj : (ℕ∪∞) × T' ⟶ (ℕ∪∞) × (ℕ∪∞)`, a surjection and hence an epimorphism. -/
def hFourPull : hFourW S ⟶ NS2 :=
  MonoidalCategory.whiskerLeft (ℕ∪{∞}) (tProj S)

/-- `(k,t) ↦ ψ(k, pr₂ t)`, the first `ℤ`-term of the left hand side of `h₄`. -/
def hFourPsi1 : hFourW S ⟶ LightProfinite.NatUnionInfty :=
  MonoidalCategory.whiskerLeft (ℕ∪{∞}) (pr₂T S) ≫ psiN S

/-- `(k,t) ↦ ψ(k, β t)`, the second `ℤ`-term of the left hand side of `h₄`. -/
def hFourPsi2 : hFourW S ⟶ LightProfinite.NatUnionInfty :=
  MonoidalCategory.whiskerLeft (ℕ∪{∞}) (betaT S) ≫ psiN S

/-- `(k,t) ↦ φ_P(k, tProj t)`, the first `ℤ`-term of the right hand side of `h₄`. -/
def hFourQ1 : hFourW S ⟶ LightProfinite.NatUnionInfty :=
  MonoidalCategory.whiskerLeft (ℕ∪{∞}) (tProj S) ≫ phiP S

/-- `(k,t) ↦ φ_P(k+1, tProj t)`, the second `ℤ`-term of the right hand side of `h₄`
(`φ_P(shift k, ·)`, so that also `k = ∞` is covered: `shift ∞ = ∞`). -/
def hFourQ2 : hFourW S ⟶ LightProfinite.NatUnionInfty :=
  MonoidalCategory.whiskerLeft (ℕ∪{∞}) (tProj S) ≫
    MonoidalCategory.whiskerRight LightProfinite.shift (ℕ∪{∞}) ≫ phiP S

/-! ## Pointwise descriptions -/

@[simp] lemma hFourPull_apply (w : ↥(hFourW S)) :
    hFourPull S w = (w.1, tProj S w.2) := rfl

@[simp] lemma hFourPsi1_apply (w : ↥(hFourW S)) :
    hFourPsi1 S w = psiFun S (w.1, pr₂T S w.2) := rfl

@[simp] lemma hFourPsi2_apply (w : ↥(hFourW S)) :
    hFourPsi2 S w = psiFun S (w.1, betaT S w.2) := rfl

@[simp] lemma hFourQ1_apply (w : ↥(hFourW S)) :
    hFourQ1 S w = phiPFun S (w.1, tProj S w.2) := rfl

lemma hFourQ2_apply (w : ↥(hFourW S)) :
    hFourQ2 S w = phiPFun S (LightProfinite.shift w.1, tProj S w.2) := rfl

/-- `ψ(k,x)` depends only on `e_k x`: this is what makes the two `ψ`-terms of `h₄` cancel for
`k < n(j)`, where `e_k a_j = e_k (e_{n(j)-1} a_j)`. -/
lemma psiFun_dep {k : ℕ} {x y : ↥S} (h : e S k x = e S k y) :
    psiFun S (((k : ℕ) : ℕ∪{∞}), x) = psiFun S (((k : ℕ) : ℕ∪{∞}), y) := by
  by_cases hx : e S k x ∈ Set.range (levelData S).a ∧ (levelData S).lv (e S k x) = k
  · rw [psiFun_some_of k hx, psiFun_some_of k (h ▸ hx), h]
  · rw [psiFun_some_eq_infty k hx, psiFun_some_eq_infty k (h ▸ hx)]

/-! ## The two closed pieces -/

/-- The piece where both sides of `h₄` vanish: `ψ₁ = ψ₂` and `φ₁ = φ₂`. -/
def hFourCA : Set ↥(hFourW S) :=
  {w | hFourPsi1 S w = hFourPsi2 S w ∧ hFourQ1 S w = hFourQ2 S w}

/-- The piece where the two sides of `h₄` agree term by term: `ψ₁ = φ₁` and `ψ₂ = φ₂`. -/
def hFourCB : Set ↥(hFourW S) :=
  {w | hFourPsi1 S w = hFourQ1 S w ∧ hFourPsi2 S w = hFourQ2 S w}

lemma isClosed_hFourCA : IsClosed (hFourCA S) := by
  rw [show hFourCA S =
      {w : ↥(hFourW S) | hFourPsi1 S w = hFourPsi2 S w} ∩
        {w : ↥(hFourW S) | hFourQ1 S w = hFourQ2 S w} by
    ext w; simp [hFourCA]]
  exact (isClosed_eq (ConcreteCategory.hom (hFourPsi1 S)).continuous
      (ConcreteCategory.hom (hFourPsi2 S)).continuous).inter
    (isClosed_eq (ConcreteCategory.hom (hFourQ1 S)).continuous
      (ConcreteCategory.hom (hFourQ2 S)).continuous)

lemma isClosed_hFourCB : IsClosed (hFourCB S) := by
  rw [show hFourCB S =
      {w : ↥(hFourW S) | hFourPsi1 S w = hFourQ1 S w} ∩
        {w : ↥(hFourW S) | hFourPsi2 S w = hFourQ2 S w} by
    ext w; simp [hFourCB]]
  exact (isClosed_eq (ConcreteCategory.hom (hFourPsi1 S)).continuous
      (ConcreteCategory.hom (hFourQ1 S)).continuous).inter
    (isClosed_eq (ConcreteCategory.hom (hFourPsi2 S)).continuous
      (ConcreteCategory.hom (hFourQ2 S)).continuous)

instance instCompactSpaceHFourCA : CompactSpace ↥(hFourCA S) :=
  isCompact_iff_compactSpace.mp (isClosed_hFourCA S).isCompact

instance instCompactSpaceHFourCB : CompactSpace ↥(hFourCB S) :=
  isCompact_iff_compactSpace.mp (isClosed_hFourCB S).isCompact

/-- The first closed piece of the cover, as a light profinite set. -/
noncomputable def hFourCApiece : LightProfinite.{0} := LightProfinite.of ↥(hFourCA S)

/-- The second closed piece of the cover, as a light profinite set. -/
noncomputable def hFourCBpiece : LightProfinite.{0} := LightProfinite.of ↥(hFourCB S)

/-- The inclusion of the first piece. -/
noncomputable def hFourICA : hFourCApiece S ⟶ hFourW S :=
  ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of the second piece. -/
noncomputable def hFourICB : hFourCBpiece S ⟶ hFourW S :=
  ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp] lemma hFourICA_apply (w : ↥(hFourCApiece S)) : hFourICA S w = w.1 := rfl
@[simp] lemma hFourICB_apply (w : ↥(hFourCBpiece S)) : hFourICB S w = w.1 := rfl

/-- The point `(k,t)` of `hFourW S = (ℕ∪∞) ⊗ T'` (an `abbrev` so that the pair is accepted
against the underlying type of the product). -/
abbrev hFourMk (k : LightProfinite.NatUnionInfty) (t : ↥(T' S)) : ↥(hFourW S) := (k, t)

/-- `hFourPull = id × tProj` is surjective, because `tProj : T' ⟶ ℕ∪∞` is. -/
theorem hFourPull_surjective : Function.Surjective (hFourPull S) := by
  rintro ⟨k, j⟩
  obtain ⟨t, ht⟩ := tProj_surjective S j
  refine ⟨hFourMk S k t, ?_⟩
  rw [hFourPull_apply]
  exact Prod.ext rfl ht

/-- On the first piece the two `ψ`-terms agree (and the two `φ`-terms agree). -/
lemma hFourICA_psi : hFourICA S ≫ hFourPsi1 S = hFourICA S ≫ hFourPsi2 S := by
  apply ConcreteCategory.hom_ext
  intro w
  exact w.2.1

/-- On the first piece the two `φ`-terms agree. -/
lemma hFourICA_q : hFourICA S ≫ hFourQ1 S = hFourICA S ≫ hFourQ2 S := by
  apply ConcreteCategory.hom_ext
  intro w
  exact w.2.2

/-- On the second piece `ψ₁ = φ₁`. -/
lemma hFourICB_psi1 : hFourICB S ≫ hFourPsi1 S = hFourICB S ≫ hFourQ1 S := by
  apply ConcreteCategory.hom_ext
  intro w
  exact w.2.1

/-- On the second piece `ψ₂ = φ₂`. -/
lemma hFourICB_psi2 : hFourICB S ≫ hFourPsi2 S = hFourICB S ≫ hFourQ2 S := by
  apply ConcreteCategory.hom_ext
  intro w
  exact w.2.2

/-- The first piece is contained in the range of `hFourICA`. -/
lemma mem_range_hFourICA {w : ↥(hFourW S)} (hw : w ∈ hFourCA S) :
    w ∈ Set.range (ConcreteCategory.hom (hFourICA S)) := ⟨⟨w, hw⟩, rfl⟩

/-- The second piece is contained in the range of `hFourICB`. -/
lemma mem_range_hFourICB {w : ↥(hFourW S)} (hw : w ∈ hFourCB S) :
    w ∈ Set.range (ConcreteCategory.hom (hFourICB S)) := ⟨⟨w, hw⟩, rfl⟩

/-! ## The two-piece cover as a family of light profinite sets -/

/-- The two-piece closed cover of `hFourW S` (`Fin 2`-indexed). -/
noncomputable def hFourCover : Fin 2 → LightProfinite.{0}
  | 0 => hFourCApiece S
  | 1 => hFourCBpiece S

/-- The inclusions of the two pieces into `hFourW S`. -/
noncomputable def hFourCoverι (i : Fin 2) : hFourCover S i ⟶ hFourW S :=
  match i with
  | 0 => hFourICA S
  | 1 => hFourICB S

@[simp] lemma hFourCover_zero : hFourCover S 0 = hFourCApiece S := rfl
@[simp] lemma hFourCover_one : hFourCover S 1 = hFourCBpiece S := rfl
@[simp] lemma hFourCoverι_zero : hFourCoverι S 0 = hFourICA S := rfl
@[simp] lemma hFourCoverι_one : hFourCoverι S 1 = hFourICB S := rfl

end Work.ATOM.ZS
