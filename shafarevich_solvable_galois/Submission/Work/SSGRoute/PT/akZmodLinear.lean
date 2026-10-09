import Mathlib
import Submission.Work.SSGRoute.PT.alphaOneLayer
import Submission.Work.SSGRoute.PT.ker_le_range_precompHom
import Submission.Work.SSGRoute.PTembedding.localKummer_base
import Submission.Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `𝔽_p`-linearity of the continuous cohomology functor, and the first `precompHom`-exactness

`PTembedding/localKummer_base.lean` gives the continuous cohomology `H¹_c(Γ,M)` of the
`AbsoluteKummer` model its `𝔽_p`-module structure (`instModuleH1c`), but the induced maps
`mapZ1`/`mapH1` were not known to be `𝔽_p`-linear.  Without that linearity the *range* of
`mapH1 ψ` is not a submodule of `H¹_c(Γ,N₁)`, so the exactness of the bottom row of Milne's
diagram (1.9.1) cannot be applied to it.

This file supplies the linearity (`mapZ1_smul`, `mapH1_smul`) at the universe level of the
`localKummer_base` instances, and then the first `ebot` input of
`PT.alphaOne_bijective_of_devissage` — the exactness at `(H¹(N₂))^∨`:

  `Function.Exact (transpMapH1 ψ hψ) (transpMapH1' φ hφ)`

for an `𝔽_p`-linear `ψ` and the module long exact sequence's exactness at `H¹(N₂)`.

Since the cohomology `H¹_c` is not (yet) known to be a `𝔽_p`-module in a universe-polymorphic way,
everything below is at universe `0`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

namespace AKZmodLin

/-! ## `Function.Exact` from `range = ker`, and the `𝔽_p`-splitting of a range -/

/-- **`Function.Exact` from `range = ker`** for additive maps (the form in which the workspace's
long exact sequences state their exactness). -/
theorem functionExact_of_range_eq_ker {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] {f : A →+ B} {g : B →+ C} (h : f.range = g.ker) :
    Function.Exact (⇑f) (⇑g) := by
  intro y
  rw [Set.mem_range]
  constructor
  · intro hy
    exact AddMonoidHom.mem_range.mp (h.symm ▸ (AddMonoidHom.mem_ker.mpr hy))
  · rintro ⟨x, rfl⟩
    exact AddMonoidHom.mem_ker.mp (h ▸ (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩))

/-- **The range of a `𝔽_p`-linear map is a direct summand**: an additive retraction of the
inclusion `range g ↪ C`, in the form consumed by `PT.ker_le_range_precompHom`. -/
theorem zmod_retraction_range {p : ℕ} [Fact p.Prime]
    {B : Type} [AddCommGroup B] [Module (ZMod p) B]
    {C : Type} [AddCommGroup C] [Module (ZMod p) C]
    (g : B →+ C) (hg : ∀ (c : ZMod p) (b : B), g (c • b) = c • g b) :
    ∃ r : C →+ ↥(g.range), ∀ y : ↥(g.range), r (y : C) = y := by
  let S : Submodule (ZMod p) C :=
    { carrier := (g.range : Set C)
      zero_mem' := g.range.zero_mem
      add_mem' := fun ha hb => g.range.add_mem ha hb
      smul_mem' := fun c b hb => by
        obtain ⟨x, rfl⟩ := hb
        exact ⟨c • x, hg c x⟩ }
  obtain ⟨K, hK⟩ := S.exists_isCompl
  let i : ↥S →ₗ[ZMod p] C := S.subtype
  have hi : Function.Injective i := fun x y h => Subtype.ext h
  have hrange : LinearMap.range i = S := Submodule.range_subtype S
  have hcompl : IsCompl (LinearMap.range i) K := by rw [hrange]; exact hK
  let proj : C →ₗ[ZMod p] ↥S := LinearMap.linearProjOfIsCompl K i hi hcompl
  exact ⟨proj.toAddMonoidHom, fun y => by
    show proj (y : C) = y
    have : (y : C) = i y := rfl
    rw [this]
    exact LinearMap.linearProjOfIsCompl_apply_left K i hi hcompl y⟩

/-- **The bottom row is exact in the `𝔽_p` setting**: for `𝔽_p`-linear `f, g` with
`f.range = g.ker`, the transposed maps are exact at the middle term. -/
theorem precompHom_range_eq_ker_of_zmod {p : ℕ} [Fact p.Prime]
    {A : Type} [AddCommGroup A]
    {B : Type} [AddCommGroup B] [Module (ZMod p) B]
    {C : Type} [AddCommGroup C] [Module (ZMod p) C]
    {X : Type} [AddCommGroup X]
    (f : A →+ B) (g : B →+ C) (hg : ∀ (c : ZMod p) (b : B), g (c • b) = c • g b)
    (hex : f.range = g.ker) :
    (precompHom (X := X) g).range = (precompHom (X := X) f).ker := by
  refine le_antisymm ?_ ?_
  · intro ψ hψ
    obtain ⟨φ, rfl⟩ := AddMonoidHom.mem_range.mp hψ
    rw [AddMonoidHom.mem_ker]
    ext a
    show φ (g (f a)) = 0
    have hgf : g (f a) = 0 :=
      AddMonoidHom.mem_ker.mp (hex ▸ (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩))
    rw [hgf, map_zero]
  · intro χ hχ
    rw [AddMonoidHom.mem_ker] at hχ
    obtain ⟨r, hr⟩ := zmod_retraction_range (p := p) g hg
    obtain ⟨θ, hθ⟩ := ker_le_range_precompHom f g hex r hr χ
      (fun a => by
        have h := DFunLike.congr_fun hχ a
        simpa only [precompHom_apply, AddMonoidHom.zero_apply] using h)
    exact AddMonoidHom.mem_range.mpr ⟨θ, hθ⟩

/-! ## Linearity of `mapZ1` and `mapH1` -/

section Linearity

variable {p : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The scalar action of `instModuleH1c` on the quotient is the quotient scalar action. -/
theorem smul_H1π {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] (c : ZMod p) (f : Work.AbsoluteKummer.Z1 G M) :
    c • Work.AbsoluteKummer.H1π G M f = Work.AbsoluteKummer.H1π G M (c • f) := rfl

/-- **`mapZ1` is `𝔽_p`-linear** for an `𝔽_p`-linear equivariant `φ`. -/
theorem mapZ1_smul {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    {N : Type} [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N]
    (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hlin : ∀ (c : ZMod p) (m : M), φ (c • m) = c • φ m)
    (c : ZMod p) (f : Work.AbsoluteKummer.Z1 G M) :
    Work.AbsoluteKummer.mapZ1 φ hφ (c • f) = c • Work.AbsoluteKummer.mapZ1 φ hφ f := by
  refine Subtype.ext (funext fun g => ?_)
  simp only [Work.AbsoluteKummer.mapZ1_apply,
    Work.SSGRoute.PTembedding.instModuleZ1c_coe_smul, Pi.smul_apply]
  exact hlin c ((f : G → M) g)

/-- **`mapH1` is `𝔽_p`-linear** for an `𝔽_p`-linear equivariant `φ`.  This is what makes
`(mapH1 ψ).range` a submodule. -/
theorem mapH1_smul {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    {N : Type} [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N]
    (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hlin : ∀ (c : ZMod p) (m : M), φ (c • m) = c • φ m)
    (c : ZMod p) (x : Work.AbsoluteKummer.H1 G M) :
    Work.AbsoluteKummer.mapH1 φ hφ (c • x) = c • Work.AbsoluteKummer.mapH1 φ hφ x := by
  refine Work.AbsoluteKummer.SES.H1_induction_on
    (C := fun x => Work.AbsoluteKummer.mapH1 φ hφ (c • x)
      = c • Work.AbsoluteKummer.mapH1 φ hφ x) x ?_
  intro f
  have h2 : Work.AbsoluteKummer.mapZ1 φ hφ (c • f)
      = c • Work.AbsoluteKummer.mapZ1 φ hφ f :=
    mapZ1_smul φ hφ hlin c f
  rw [smul_H1π, Work.AbsoluteKummer.mapH1_H1π, Work.AbsoluteKummer.mapH1_H1π, h2, smul_H1π]

end Linearity

/-! ## The `𝔽_p`-module structure on the invariants, and `invariantsHom`-linearity -/

section Invariants

variable {p : ℕ} {G : Type} [Group G]

/-- **The invariants carry a `𝔽_p`-module structure** (the action of `G` being `𝔽_p`-linear, the
fixed points are an `𝔽_p`-subspace).  This mirrors `PTembedding.instModuleZ1c`. -/
noncomputable instance instModuleH0 {M : Type} [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] :
    Module (ZMod p) ↥(Work.GroupCohomology.invariants G M) where
  smul c x := ⟨c • (x : M), fun g => by
    rw [smul_comm g c (x : M), x.2 g]⟩
  one_smul x := Subtype.ext (one_smul (ZMod p) (x : M))
  mul_smul c d x := Subtype.ext (mul_smul c d (x : M))
  smul_zero c := Subtype.ext (smul_zero c)
  smul_add c x y := Subtype.ext (smul_add c (x : M) (y : M))
  add_smul c d x := Subtype.ext (add_smul c d (x : M))
  zero_smul x := Subtype.ext (zero_smul (ZMod p) (x : M))

/-- The scalar action of `instModuleH0` is pointwise. -/
@[simp] theorem instModuleH0_coe_smul {M : Type} [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (c : ZMod p)
    (x : ↥(Work.GroupCohomology.invariants G M)) :
    ((c • x : ↥(Work.GroupCohomology.invariants G M)) : M) = c • (x : M) := rfl

/-- **`invariantsHom` is `𝔽_p`-linear** for an `𝔽_p`-linear equivariant `φ`. -/
theorem invariantsHom_smul {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    {N : Type} [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N]
    (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hlin : ∀ (c : ZMod p) (m : M), φ (c • m) = c • φ m)
    (c : ZMod p) (x : ↥(Work.GroupCohomology.invariants G M)) :
    invariantsHom φ hφ (c • x) = c • invariantsHom φ hφ x := by
  refine Subtype.ext ?_
  exact hlin c (x : M)

end Invariants

/-! ## The first `precompHom`-exactness of the `r = 1` descent -/

section EbotOne

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
  {N : Type} [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
  [SMulCommClass G (ZMod p) N]
  {N₁ : Type} [AddCommGroup N₁] [Module (ZMod p) N₁] [DistribMulAction G N₁]
  [SMulCommClass G (ZMod p) N₁]
  {N₂ : Type} [AddCommGroup N₂] [Module (ZMod p) N₂] [DistribMulAction G N₂]
  [SMulCommClass G (ZMod p) N₂]
  {C : Type} [AddCommGroup C] [DistribMulAction G C]

/-- **`ebot₁` of the `r = 1` descent**: for an `𝔽_p`-linear equivariant `ψ : N₂ →+ N₁` and the
module long exact sequence's exactness `(mapH1 φ).range = (mapH1 ψ).ker` at `H¹(N₂)`, the
transposed row is exact at `(H¹(N₂))^∨`. -/
theorem exact_transpMapH1_of_zmod
    (φ : N →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (ψ : N₂ →+ N₁) (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hlinψ : ∀ (c : ZMod p) (n : N₂), ψ (c • n) = c • ψ n)
    (hex : (Work.AbsoluteKummer.mapH1 φ hφ).range
      = (Work.AbsoluteKummer.mapH1 ψ hψ).ker) :
    Function.Exact
      (transpMapH1 (G := G) (N₁ := N₁) (N₂ := N₂) (C := C) ψ hψ)
      (transpMapH1' (G := G) (N := N) (N₂ := N₂) (C := C) φ hφ) :=
  functionExact_of_range_eq_ker
    (precompHom_range_eq_ker_of_zmod (Work.AbsoluteKummer.mapH1 φ hφ)
      (Work.AbsoluteKummer.mapH1 ψ hψ) (fun c x => mapH1_smul ψ hψ hlinψ c x) hex)


/-- **`ebot₂` of the `r = 1` descent**: for a `𝔽_p`-linear connecting map `δm` and the module long
exact sequence's exactness `δm.range = (mapH1 φ).ker` at `H¹(N)`, the transposed row is exact at
`(H¹(N))^∨`. -/
theorem exact_transpDelta_of_zmod
    (φ : N →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hlinφ : ∀ (c : ZMod p) (n : N), φ (c • n) = c • φ n)
    (δm : Work.AbsoluteKummer.H0 G N₁ →+ Work.AbsoluteKummer.H1 G N)
    (hlinδm : ∀ (c : ZMod p) (x : Work.AbsoluteKummer.H0 G N₁), δm (c • x) = c • δm x)
    (hex : δm.range = (Work.AbsoluteKummer.mapH1 φ hφ).ker) :
    Function.Exact
      (transpMapH1' (G := G) (N := N) (N₂ := N₂) (C := C) φ hφ)
      (transpDelta (G := G) (N := N) (N₁ := N₁) (C := C) δm) :=
  functionExact_of_range_eq_ker
    (precompHom_range_eq_ker_of_zmod δm (Work.AbsoluteKummer.mapH1 φ hφ)
      (fun c x => mapH1_smul φ hφ hlinφ c x) hex)

/-- **`ebot₃` of the `r = 1` descent**: for a `𝔽_p`-linear connecting map `δm` and the module long
exact sequence's exactness `(invariantsHom ψ).range = δm.ker`, the transposed row is exact at
`(H⁰(N₁))^∨`. -/
theorem exact_transpInvariants_of_zmod
    (ψ : N₂ →+ N₁) (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hlinψ : ∀ (c : ZMod p) (n : N₂), ψ (c • n) = c • ψ n)
    (δm : Work.AbsoluteKummer.H0 G N₁ →+ Work.AbsoluteKummer.H1 G N)
    (hlinδm : ∀ (c : ZMod p) (x : Work.AbsoluteKummer.H0 G N₁), δm (c • x) = c • δm x)
    (hex : (invariantsHom ψ hψ).range = δm.ker) :
    Function.Exact
      (transpDelta (G := G) (N := N) (N₁ := N₁) (C := C) δm)
      (transpInvariants (G := G) (N₁ := N₁) (N₂ := N₂) (C := C) ψ hψ) :=
  functionExact_of_range_eq_ker
    (precompHom_range_eq_ker_of_zmod (invariantsHom ψ hψ) δm hlinδm hex)
end EbotOne

end AKZmodLin

end Work.SSGRoute.PT
