import Mathlib
import Submission.Work.ConCohomology.All

/-!
# `Work.ShafarevichKoch.Gaschutz.Cup` -- the cup product `H¹ × H¹ → H²` for continuous cohomology

Mathlib has no cup product; the classical proofs of the two arithmetic inputs of this chapter
(Koch, *Galois theory of `p`-extensions*, Ch. 11 Thm 11.3: `Sha_S ↪ (V_S/(K^×)^p)^∨`, and Wingberg's
duality `Ĥ^i(G_∅,O^×) ≅ Ĥ^{3-i}(G_∅,ℤ)^∨`) both pair a `2`-cocycle with the *Kummer class* of an
element of `V_S`, i.e. they use the cup product.  This module builds the first primitive of that
route: for a topological group `G` and a commutative ring `R` with *trivial* action, the cup product
of two `1`-cochains

```
(f ∪ g) (σ, τ) := f σ * g τ
```

is a `2`-cochain; it satisfies the Leibniz rule
`d²(f ∪ g) = d¹f ∪ g - f ∪ d¹g` (hence is a `2`-cocycle as soon as `f` and `g` are `1`-cocycles);
and, because for a trivial action `B¹ = 0`, it descends to a **bilinear** map

```
∪ : H¹(G,R) → H¹(G,R) → H²(G,R).
```

Everything here is elementary: the Leibniz rule is `ring`, and the descent uses
`Work.ConCohomology.B1'_eq_bot` (`H¹ = Z¹` for trivial coefficients).

## Main declarations

* `Work.ShafarevichKoch.cupFun`, `Work.ShafarevichKoch.isLocallyConstant_cupFun`,
  `Work.ShafarevichKoch.d2Fun_cupFun`;
* `Work.ShafarevichKoch.cupZ1` (the cup product of two `1`-cocycles, as a `2`-cocycle) with its
  bilinearity `cupZ1_add_left`, `cupZ1_add_right`;
* `Work.ShafarevichKoch.cupH1` and its bilinearity `cupH1_add_left`, `cupH1_add_right`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {R : Type*} [CommRing R] [DistribMulAction G R] [IsDiscreteGModule G R]

/-- **The cup product of two `1`-cochains**: `(f ∪ g)(σ,τ) = f σ * g τ`. -/
def cupFun (f g : G → R) : G × G → R := fun p => f p.1 * g p.2

/-- The cup product of locally constant `1`-cochains is locally constant. -/
theorem isLocallyConstant_cupFun {f g : G → R} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : IsLocallyConstant (cupFun f g) :=
  (hf.comp_continuous continuous_fst).mul (hg.comp_continuous continuous_snd)

/-- **The Leibniz rule for the cup product of `1`-cochains**:
`d²(f ∪ g) = (d¹f) * g - f * (d¹g)`, for a trivial action on the coefficients. -/
theorem d2Fun_cupFun (f g : G → R) (htriv : ∀ (σ : G) (r : R), σ • r = r) :
    d2Fun (cupFun f g) = fun p : G × G × G =>
      d1Fun f (p.1, p.2.1) * g p.2.2 - f p.1 * d1Fun g (p.2.1, p.2.2) := by
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [d2Fun_apply, cupFun, d1Fun_apply, htriv]
  ring

/-- **The cup product of two `1`-cocycles is a `2`-cocycle.** -/
theorem isCocycle2_cupFun {f g : G → R} (hf : IsCocycle1 f) (hg : IsCocycle1 g)
    (htriv : ∀ (σ : G) (r : R), σ • r = r) : IsCocycle2 (cupFun f g) := by
  rw [isCocycle2_iff_d2Fun, d2Fun_cupFun f g htriv]
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  have hf0 : d1Fun f (σ, τ) = 0 := by
    have h := congrFun ((isCocycle1_iff_d1Fun f).mp hf) (σ, τ)
    simpa using h
  have hg0 : d1Fun g (τ, ρ) = 0 := by
    have h := congrFun ((isCocycle1_iff_d1Fun g).mp hg) (τ, ρ)
    simpa using h
  rw [hf0, hg0]
  simp

/-- **The cup product of two `1`-cocycles, as a `2`-cocycle.** -/
def cupZ1 (htriv : ∀ (σ : G) (r : R), σ • r = r) (f g : Z1 G R) : Z2 G R :=
  ⟨⟨cupFun (f : G → R) (g : G → R),
      isLocallyConstant_cupFun f.1.isLocallyConstant g.1.isLocallyConstant⟩,
    mem_Z2.mpr (isCocycle2_cupFun (mem_Z1.mp f.2) (mem_Z1.mp g.2) htriv)⟩

@[simp] lemma cupZ1_coe (htriv : ∀ (σ : G) (r : R), σ • r = r) (f g : Z1 G R) :
    ((cupZ1 htriv f g : Z2 G R) : Cochain2 G R) = ⟨cupFun (f : G → R) (g : G → R),
      isLocallyConstant_cupFun f.1.isLocallyConstant g.1.isLocallyConstant⟩ := rfl

/-- **Linearity of the cup product in the left variable.** -/
theorem cupZ1_add_left (htriv : ∀ (σ : G) (r : R), σ • r = r) (f₁ f₂ g : Z1 G R) :
    cupZ1 htriv (f₁ + f₂) g = cupZ1 htriv f₁ g + cupZ1 htriv f₂ g := by
  apply Subtype.ext
  apply LocallyConstant.ext
  rintro ⟨σ, τ⟩
  simp only [cupZ1, cupFun, AddSubgroup.coe_add, AddSubgroup.coe_mk, AddMonoidHom.add_apply,
    LocallyConstant.coe_add, LocallyConstant.coe_mk, Pi.add_apply]
  ring

/-- **Linearity of the cup product in the right variable.** -/
theorem cupZ1_add_right (htriv : ∀ (σ : G) (r : R), σ • r = r) (f g₁ g₂ : Z1 G R) :
    cupZ1 htriv f (g₁ + g₂) = cupZ1 htriv f g₁ + cupZ1 htriv f g₂ := by
  apply Subtype.ext
  apply LocallyConstant.ext
  rintro ⟨σ, τ⟩
  simp only [cupZ1, cupFun, AddSubgroup.coe_add, AddSubgroup.coe_mk, AddMonoidHom.add_apply,
    LocallyConstant.coe_add, LocallyConstant.coe_mk, Pi.add_apply]
  ring

/-- **The cup product descends to cohomology in the left variable.**  For a trivial action
`H¹(G,R) = Z¹(G,R)` (since `B¹ = 0`), so cohomologous `1`-cocycles have cohomologous cup products. -/
theorem cupZ1_mk_eq_of_mk_eq_left (htriv : ∀ (σ : G) (r : R), σ • r = r) {f f' : Z1 G R}
    (h : H1.mk f = H1.mk f') (y : Z1 G R) :
    H2.mk (cupZ1 htriv f y) = H2.mk (cupZ1 htriv f' y) := by
  have hbot : f - f' ∈ B1' G R := (H1.mk_eq_mk_iff f f').mp h
  rw [B1'_eq_bot htriv, AddSubgroup.mem_bot] at hbot
  have hff : f = f' := sub_eq_zero.mp hbot
  rw [hff]

/-- **The cup product descends to cohomology in the right variable.** -/
theorem cupZ1_mk_eq_of_mk_eq_right (htriv : ∀ (σ : G) (r : R), σ • r = r) (f : Z1 G R)
    {g g' : Z1 G R} (h : H1.mk g = H1.mk g') :
    H2.mk (cupZ1 htriv f g) = H2.mk (cupZ1 htriv f g') := by
  have hbot : g - g' ∈ B1' G R := (H1.mk_eq_mk_iff g g').mp h
  rw [B1'_eq_bot htriv, AddSubgroup.mem_bot] at hbot
  have hgg : g = g' := sub_eq_zero.mp hbot
  rw [hgg]

/-- **The cup product on cohomology**, `H¹(G,R) × H¹(G,R) → H²(G,R)`, for a trivial action: the
cup product of any two representatives (well defined by the two lemmas above). -/
noncomputable def cupH1 (htriv : ∀ (σ : G) (r : R), σ • r = r) (x y : H1 G R) : H2 G R :=
  H2.mk (cupZ1 htriv (Quotient.out x) (Quotient.out y))

/-- The defining property of `cupH1` on representatives. -/
theorem cupH1_mk (htriv : ∀ (σ : G) (r : R), σ • r = r) (f g : Z1 G R) :
    cupH1 htriv (H1.mk f) (H1.mk g) = H2.mk (cupZ1 htriv f g) := by
  unfold cupH1
  have hf : H1.mk (Quotient.out (H1.mk f)) = H1.mk f := Quotient.out_eq (H1.mk f)
  have hg : H1.mk (Quotient.out (H1.mk g)) = H1.mk g := Quotient.out_eq (H1.mk g)
  have h₁ : H2.mk (cupZ1 htriv (Quotient.out (H1.mk f)) (Quotient.out (H1.mk g)))
      = H2.mk (cupZ1 htriv f (Quotient.out (H1.mk g))) :=
    (cupZ1_mk_eq_of_mk_eq_left htriv hf.symm _).symm
  have h₂ : H2.mk (cupZ1 htriv f (Quotient.out (H1.mk g))) = H2.mk (cupZ1 htriv f g) :=
    (cupZ1_mk_eq_of_mk_eq_right htriv f hg.symm).symm
  exact h₁.trans h₂
