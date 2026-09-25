/-
Copyright: the martinet_totally_real_towers team.

# The Kummer sequence

For a discrete `G`-module `B` and `n : ℕ`, the `n`-th power map `x ↦ n • x` (`x ↦ xⁿ`) is an
equivariant endomorphism of `B` (`nsmulEqHom`), with kernel the `n`-torsion subgroup `μ_n`
(`nTorsion`) and image the subgroup of `n`-th powers (`nPowers`).  The resulting short exact
sequence

`0 → μ_n → B →ⁿ n·B → 0`

is `kummerSES`.  Taking `B = Additive Lˣ` and `G = Gal(L/K)` gives the Kummer sequence
`1 → μ_n → Lˣ →ⁿ (Lˣ)ⁿ → 1`; the discreteness instances
`instIsDiscreteGModuleKer` / `instIsDiscreteGModuleRange` are inherited from `B`, and for
`L = K^sep` every element of `Kˣ` is an `n`-th power (so `nPowers = ⊤` on the relevant part).
The consequences for cohomology are `Work.ConCohomology.kummer_H1_surjective` and
`Work.ConCohomology.kummer_H2_injective` (see `README.md`).
-/

import Submission.Work.ConCohomology.Setup

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section Base

variable {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [DistribMulAction G B]

/-- `n • (x + y) = n • x + n • y`. -/
lemma nsmul_add_apply (n : ℕ) (x y : B) : n • (x + y) = n • x + n • y := by
  induction n with
  | zero => simp
  | succ k ih => simp only [succ_nsmul, ih]; abel

/-- `n • (σ • x) = σ • (n • x)`. -/
lemma nsmul_smul_comm (n : ℕ) (σ : G) (x : B) : n • (σ • x) = σ • (n • x) := by
  induction n with
  | zero => simp
  | succ k ih => rw [succ_nsmul, succ_nsmul, ih, smul_add]

/-- The `n`-th power endomorphism `x ↦ n • x` (multiplicatively `x ↦ xⁿ`) of a `G`-module. -/
def nsmulEqHom (n : ℕ) : EqHom G B B where
  toAddMonoidHom :=
    { toFun := fun x => n • x
      map_zero' := nsmul_zero n
      map_add' := nsmul_add_apply n }
  map_smul' := nsmul_smul_comm n

@[simp] lemma nsmulEqHom_apply (n : ℕ) (x : B) :
    nsmulEqHom (G := G) n x = n • x := rfl

/-- The `n`-torsion subgroup `μ_n` of a `G`-module. -/
abbrev nTorsion (n : ℕ) : AddSubgroup B := (nsmulEqHom (G := G) n).toAddMonoidHom.ker

/-- The subgroup of `n`-th powers. -/
abbrev nPowers (n : ℕ) : AddSubgroup B := (nsmulEqHom (G := G) n).toAddMonoidHom.range

/-- The `G`-action on the kernel of an equivariant endomorphism. -/
instance instDistribMulActionKer (F : EqHom G B B) :
    DistribMulAction G ↥(F.toAddMonoidHom.ker) where
  smul g x := ⟨g • (x : B), by
    show F.toAddMonoidHom (g • (x : B)) = 0
    rw [EqHom.map_smul, show F.toAddMonoidHom (x : B) = 0 from x.2, smul_zero]⟩
  one_smul x := Subtype.ext (by
    show (1 : G) • (x : B) = (x : B)
    rw [one_smul])
  mul_smul g h x := Subtype.ext (by
    show (g * h) • (x : B) = g • (h • (x : B))
    rw [mul_smul])
  smul_zero g := Subtype.ext (by
    show g • (0 : B) = 0
    rw [smul_zero])
  smul_add g x y := Subtype.ext (by
    show g • ((x : B) + (y : B)) = g • (x : B) + g • (y : B)
    rw [smul_add])

/-- The `G`-action on the image of an equivariant endomorphism. -/
instance instDistribMulActionRange (F : EqHom G B B) :
    DistribMulAction G ↥(F.toAddMonoidHom.range) where
  smul g x := ⟨g • (x : B), by
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.mp x.2
    exact ⟨g • b, by rw [EqHom.map_smul, hb]⟩⟩
  one_smul x := Subtype.ext (by
    show (1 : G) • (x : B) = (x : B)
    rw [one_smul])
  mul_smul g h x := Subtype.ext (by
    show (g * h) • (x : B) = g • (h • (x : B))
    rw [mul_smul])
  smul_zero g := Subtype.ext (by
    show g • (0 : B) = 0
    rw [smul_zero])
  smul_add g x y := Subtype.ext (by
    show g • ((x : B) + (y : B)) = g • (x : B) + g • (y : B)
    rw [smul_add])

section Discrete

variable [TopologicalSpace G] [IsDiscreteGModule G B]

instance instIsDiscreteGModuleKer (F : EqHom G B B) :
    IsDiscreteGModule G ↥(F.toAddMonoidHom.ker) where
  isLocallyConstant_smul x := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g₀
    obtain ⟨U, hU, hgU, hUc⟩ :=
      (IsDiscreteGModule.isLocallyConstant_smul (G := G) (x : B)).exists_open g₀
    exact ⟨U, hU, hgU, fun g hg => Subtype.ext (hUc g hg)⟩

instance instIsDiscreteGModuleRange (F : EqHom G B B) :
    IsDiscreteGModule G ↥(F.toAddMonoidHom.range) where
  isLocallyConstant_smul x := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g₀
    obtain ⟨U, hU, hgU, hUc⟩ :=
      (IsDiscreteGModule.isLocallyConstant_smul (G := G) (x : B)).exists_open g₀
    exact ⟨U, hU, hgU, fun g hg => Subtype.ext (hUc g hg)⟩

instance instDistribMulActionNTorsion (n : ℕ) : DistribMulAction G ↥(nTorsion (G := G) (B := B) n) :=
  instDistribMulActionKer (nsmulEqHom (G := G) n)

instance instDistribMulActionNPowers (n : ℕ) : DistribMulAction G ↥(nPowers (G := G) (B := B) n) :=
  instDistribMulActionRange (nsmulEqHom (G := G) n)

instance instIsDiscreteGModuleNTorsion [TopologicalSpace G] [IsDiscreteGModule G B] (n : ℕ) :
    IsDiscreteGModule G ↥(nTorsion (G := G) (B := B) n) :=
  instIsDiscreteGModuleKer (nsmulEqHom (G := G) n)

instance instIsDiscreteGModuleNPowers [TopologicalSpace G] [IsDiscreteGModule G B] (n : ℕ) :
    IsDiscreteGModule G ↥(nPowers (G := G) (B := B) n) :=
  instIsDiscreteGModuleRange (nsmulEqHom (G := G) n)

/-- The power map `B → n·B`, as a homomorphism onto its image. -/
noncomputable def powToPowers (n : ℕ) : B →+ ↥(nPowers (G := G) (B := B) n) :=
  AddMonoidHom.codRestrict (nsmulEqHom (G := G) n).toAddMonoidHom _
    (fun x => AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)

@[simp] lemma powToPowers_apply (n : ℕ) (x : B) :
    ((powToPowers (G := G) n x : ↥(nPowers (G := G) (B := B) n)) : B) =
      nsmulEqHom (G := G) n x := rfl

/-- The inclusion `μ_n → B`. -/
def kummerF (n : ℕ) : EqHom G ↥(nTorsion (G := G) (B := B) n) B where
  toAddMonoidHom := AddSubgroup.subtype _
  map_smul' := fun σ a => rfl

/-- The power map `B → n·B`, as an equivariant map onto its image. -/
noncomputable def kummerG (n : ℕ) : EqHom G B ↥(nPowers (G := G) (B := B) n) where
  toAddMonoidHom := powToPowers (G := G) n
  map_smul' σ a := Subtype.ext (EqHom.map_smul (nsmulEqHom (G := G) n) σ a)

/-- The Kummer sequence `0 → μ_n → B →ⁿ n·B → 0` of discrete `G`-modules. -/
noncomputable def kummerSES (n : ℕ) :
    CoeffSES G ↥(nTorsion (G := G) (B := B) n) B ↥(nPowers (G := G) (B := B) n) where
  f := kummerF (G := G) n
  g := kummerG (G := G) n
  injective_f := Subtype.coe_injective
  surjective_g := fun c => by
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.mp c.2
    refine ⟨b, Subtype.ext ?_⟩
    show nsmulEqHom (G := G) n b = (c : B)
    simpa using hb
  exact := fun b => by
    constructor
    · intro hb
      have hb' : nsmulEqHom (G := G) n b = 0 := Subtype.ext_iff.mp hb
      exact ⟨⟨b, hb'⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact Subtype.ext a.2

end Discrete

end Base

end Work.ConCohomology
