import Mathlib
import Submission.Work.ShafarevichKoch.Cohomology3
import Submission.Work.ShafarevichKoch.Gaschutz.Cup

/-!
# `Work.ShafarevichKoch.Gaschutz.CupTwo` -- the cup product `H¹ × H² → H³`

`Gaschutz/Cup.lean` builds the cup product `H¹(G,R) × H¹(G,R) → H²(G,R)` for a commutative ring
`R` with trivial `G`-action (Mathlib has no cup product at all).  This module adds the *next*
primal of the same construction, the pairing

```
(f ∪ g)(σ,τ,ρ) := f σ * g (τ,ρ)      (f ∈ C¹, g ∈ C²),
```

with the Leibniz rule

```
d³(f ∪ g) = (d¹f) * g - f * (d²g) ,
```

from which `f ∪ g` is a `3`-cocycle as soon as `f` is a `1`-cocycle and `g` is a `2`-cocycle; and
since `H¹ = Z¹` for a trivial action (`ConCohomology.B1'_eq_bot`), the pairing descends to
cohomology, `∪ : H¹(G,R) → H²(G,R) → H³(G,R)`, bilinearly.

The second descent (in the `H²`-variable) is the interesting one: if `g - g' = d¹u` is a
`2`-coboundary then

```
f ∪ g - f ∪ g' = f ∪ d¹u = - d³(f ∪ u) ,
```

a genuine `3`-coboundary -- this is the `p = 1, q = 1` instance of the Leibniz rule applied twice,
and it is exactly the computation which, for `S = ∅`, would turn a `2`-cocycle of `G_∅` into a
function on Koch's radical (see the module docstring of `Gaschutz/Cup.lean`).

## Main declarations

* `Work.ShafarevichKoch.cupFun12`, `Work.ShafarevichKoch.isLocallyConstant_cupFun12`,
  `Work.ShafarevichKoch.d3Fun_cupFun12` (the Leibniz rule), `Work.ShafarevichKoch.isCocycle3_cupFun12`;
* `Work.ShafarevichKoch.cupZ1Z2` and its bilinearity `cupZ1Z2_add_left`, `cupZ1Z2_add_right`;
* `Work.ShafarevichKoch.cupH1H2` and its bilinearity `cupH1H2_add_left`, `cupH1H2_add_right`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {R : Type*} [CommRing R] [DistribMulAction G R] [IsDiscreteGModule G R]

/-! ## The `3`-cochain `f ∪ g` and its Leibniz rule -/

/-- **The cup product of a `1`-cochain and a `2`-cochain**: `(f ∪ g)(σ,τ,ρ) = f σ * g (τ,ρ)`. -/
def cupFun12 (f : G → R) (g : G × G → R) : G × G × G → R := fun p => f p.1 * g (p.2.1, p.2.2)

/-- The cup product of a locally constant `1`-cochain and a locally constant `2`-cochain is
locally constant. -/
theorem isLocallyConstant_cupFun12 {f : G → R} (hf : IsLocallyConstant f) {g : G × G → R}
    (hg : IsLocallyConstant g) : IsLocallyConstant (cupFun12 f g) :=
  (hf.comp_continuous continuous_fst).mul
    (hg.comp_continuous (Continuous.prodMk continuous_snd.fst continuous_snd.snd))

/-- The pointwise negative of a cup product of two locally constant `1`-cochains is locally
constant (the shape needed for the `3`-coboundary witnessing the descent in the `H²`-variable). -/
theorem isLocallyConstant_cupFunNeg {f u : G → R} (hf : IsLocallyConstant f)
    (hu : IsLocallyConstant u) : IsLocallyConstant (fun q : G × G => -(f q.1 * u q.2)) :=
  ((hf.comp_continuous continuous_fst).mul (hu.comp_continuous continuous_snd)).neg

/-- **The Leibniz rule for the cup product of a `1`-cochain and a `2`-cochain**:
`d³(f ∪ g) = (d¹f) * g - f * (d²g)`, for a trivial action on the coefficients. -/
theorem d3Fun_cupFun12 (f : G → R) (g : G × G → R)
    (htriv : ∀ (σ : G) (r : R), σ • r = r) :
    d3Fun (cupFun12 f g) = fun p : G × G × G × G =>
      d1Fun f (p.1, p.2.1) * g (p.2.2.1, p.2.2.2)
        - f p.1 * d2Fun g (p.2.1, p.2.2.1, p.2.2.2) := by
  funext p
  obtain ⟨σ, τ, ρ, υ⟩ := p
  simp only [d3Fun_apply, cupFun12, d1Fun_apply, d2Fun_apply, htriv]
  ring

/-- **The cup product of a `1`-cocycle and a `2`-cocycle is a `3`-cocycle.** -/
theorem isCocycle3_cupFun12 {f : G → R} {g : G × G → R} (hf : IsCocycle1 f)
    (hg : IsCocycle2 g) (htriv : ∀ (σ : G) (r : R), σ • r = r) :
    d3Fun (cupFun12 f g) = 0 := by
  rw [d3Fun_cupFun12 f g htriv]
  funext p
  obtain ⟨σ, τ, ρ, υ⟩ := p
  have hf0 : d1Fun f (σ, τ) = 0 := by
    have h := congrFun ((isCocycle1_iff_d1Fun f).mp hf) (σ, τ)
    simpa using h
  have hg0 : d2Fun g (τ, ρ, υ) = 0 := by
    have h := congrFun ((isCocycle2_iff_d2Fun g).mp hg) (τ, ρ, υ)
    simpa using h
  rw [hf0, hg0]
  simp

/-- `d3Hom` vanishes exactly on the functions whose `d³` vanishes. -/
lemma d3Hom_eq_zero_iff_sk (f : Cochain3 G R) : d3Hom G R f = 0 ↔ d3Fun (f : G × G × G → R) = 0 := by
  constructor
  · intro h
    have := congrArg (fun g : Cochain4 G R => (g : G × G × G × G → R)) h
    simpa [d3Hom] using this
  · intro h
    ext p
    simp [d3Hom, h]

/-- **The cup product of a `1`-cocycle and a `2`-cocycle, as a `3`-cocycle.** -/
def cupZ1Z2 (htriv : ∀ (σ : G) (r : R), σ • r = r) (f : Z1 G R) (g : Z2 G R) : Z3 G R :=
  ⟨⟨cupFun12 (f : G → R) (g : G × G → R),
      isLocallyConstant_cupFun12 f.1.isLocallyConstant g.1.isLocallyConstant⟩,
    mem_Z3.mpr (d3Hom_eq_zero_iff_sk _ |>.mpr
      (isCocycle3_cupFun12 (mem_Z1.mp f.2) (mem_Z2.mp g.2) htriv))⟩

@[simp] lemma cupZ1Z2_coe (htriv : ∀ (σ : G) (r : R), σ • r = r) (f : Z1 G R) (g : Z2 G R) :
    ((cupZ1Z2 htriv f g : Z3 G R) : Cochain3 G R) = ⟨cupFun12 (f : G → R) (g : G × G → R),
      isLocallyConstant_cupFun12 f.1.isLocallyConstant g.1.isLocallyConstant⟩ := rfl

/-- **Linearity of the pairing in the left variable.** -/
theorem cupZ1Z2_add_left (htriv : ∀ (σ : G) (r : R), σ • r = r) (f₁ f₂ : Z1 G R) (g : Z2 G R) :
    cupZ1Z2 htriv (f₁ + f₂) g = cupZ1Z2 htriv f₁ g + cupZ1Z2 htriv f₂ g := by
  apply Subtype.ext
  apply LocallyConstant.ext
  rintro ⟨σ, τ, ρ⟩
  simp only [cupZ1Z2, cupFun12, AddSubgroup.coe_add, AddSubgroup.coe_mk, AddMonoidHom.add_apply,
    LocallyConstant.coe_add, LocallyConstant.coe_mk, Pi.add_apply]
  ring

/-- **Linearity of the pairing in the right variable.** -/
theorem cupZ1Z2_add_right (htriv : ∀ (σ : G) (r : R), σ • r = r) (f : Z1 G R) (g₁ g₂ : Z2 G R) :
    cupZ1Z2 htriv f (g₁ + g₂) = cupZ1Z2 htriv f g₁ + cupZ1Z2 htriv f g₂ := by
  apply Subtype.ext
  apply LocallyConstant.ext
  rintro ⟨σ, τ, ρ⟩
  simp only [cupZ1Z2, cupFun12, AddSubgroup.coe_add, AddSubgroup.coe_mk, AddMonoidHom.add_apply,
    LocallyConstant.coe_add, LocallyConstant.coe_mk, Pi.add_apply]
  ring

/-! ## Descent to cohomology -/

/-! ## Descent to cohomology -/

/-- `H¹` is additive for the quotient map: `mk (a + b) = mk a + mk b`. -/
@[simp] lemma H1_mk_add (a b : Z1 G R) : H1.mk (a + b) = H1.mk a + H1.mk b :=
  (QuotientAddGroup.mk_add (B1' G R) a b).symm

/-- `H²` is additive for the quotient map: `mk (a + b) = mk a + mk b`. -/
@[simp] lemma H2_mk_add (a b : Z2 G R) : H2.mk (a + b) = H2.mk a + H2.mk b :=
  (QuotientAddGroup.mk_add (B2' G R) a b).symm

/-- `H³` is additive for the quotient map: `mk (a + b) = mk a + mk b`. -/
@[simp] lemma H3_mk_add (a b : Z3 G R) : H3.mk (a + b) = H3.mk a + H3.mk b :=
  (QuotientAddGroup.mk_add (B3' G R) a b).symm

/-- **The pairing descends to cohomology in the left variable.**  For a trivial action
`H¹(G,R) = Z¹(G,R)` (since `B¹ = 0`), so cohomologous `1`-cocycles have cohomologous cup products. -/
theorem cupZ1Z2_mk_eq_of_mk_eq_left (htriv : ∀ (σ : G) (r : R), σ • r = r) {f f' : Z1 G R}
    (h : H1.mk f = H1.mk f') (y : Z2 G R) :
    H3.mk (cupZ1Z2 htriv f y) = H3.mk (cupZ1Z2 htriv f' y) := by
  have hbot : f - f' ∈ B1' G R := (H1.mk_eq_mk_iff f f').mp h
  rw [B1'_eq_bot htriv, AddSubgroup.mem_bot] at hbot
  have hff : f = f' := sub_eq_zero.mp hbot
  rw [hff]

/-- **The pairing descends to cohomology in the right variable.**  This is the Leibniz rule
`d³(f ∪ g) = (d¹f) * g - f * (d²g)` applied to a `2`-coboundary `g - g' = d¹u`: with `f` a
`1`-cocycle the Leibniz rule reads `d³(f ∪ u) = - f * (d¹u)`, i.e.

```
f ∪ d¹u = - d³(f ∪ u) ,
```

a genuine `3`-coboundary.  (The cocycle condition on `f` is what makes the sign come out.) -/
theorem cupZ1Z2_mk_eq_of_mk_eq_right (htriv : ∀ (σ : G) (r : R), σ • r = r) (f : Z1 G R)
    {g g' : Z2 G R} (h : H2.mk g = H2.mk g') :
    H3.mk (cupZ1Z2 htriv f g) = H3.mk (cupZ1Z2 htriv f g') := by
  -- `g - g'` is a `2`-coboundary, i.e. `d¹ u` for some `1`-cochain `u`
  have hmem : g - g' ∈ B2' G R := (H2.mk_eq_mk_iff g g').mp h
  rw [mem_B2'] at hmem
  obtain ⟨u, hu⟩ := (mem_B2 (G := G) (M := R)).mp hmem
  -- the difference of the cup products is the cup product with the difference
  have hdiff : cupZ1Z2 htriv f (g - g') = cupZ1Z2 htriv f g - cupZ1Z2 htriv f g' := by
    have h := cupZ1Z2_add_right htriv f (g - g') g'
    rw [sub_add_cancel] at h
    rw [h, add_sub_cancel_right]
  rw [H3.mk_eq_mk_iff, ← hdiff, mem_B3']
  -- the `3`-coboundary witnessing it is `- (f ∪ u)`
  refine ⟨⟨fun q : G × G => -((f : G → R) q.1 * (u : G → R) q.2),
      isLocallyConstant_cupFunNeg f.1.isLocallyConstant u.isLocallyConstant⟩, ?_⟩
  have hf0fun : d1Fun (f : G → R) = 0 :=
    (isCocycle1_iff_d1Fun (f : G → R)).mp (mem_Z1.mp f.2)
  have hcoe' : ∀ σ τ : G,
      (((g - g' : Z2 G R)) : Cochain2 G R) (σ, τ) = d1Fun (u : G → R) (σ, τ) := by
    intro σ τ
    have h2 := congrFun (congrArg (fun z : Cochain2 G R => (⇑z : G × G → R)) hu) (σ, τ)
    have h3 : (d1Hom G R u : Cochain2 G R) (σ, τ) = d1Fun (u : G → R) (σ, τ) := by
      simp [d1Hom_apply]
    rw [← h2, h3]
  apply LocallyConstant.ext
  intro p
  obtain ⟨σ, τ, ρ⟩ := p
  have hcoc : (f : G → R) (σ * τ) = (f : G → R) σ + (f : G → R) τ := by
    have hh := congrFun hf0fun (σ, τ)
    simp only [d1Fun_apply, htriv, Pi.zero_apply] at hh
    linear_combination (-1) * hh
  show d2Fun (fun q : G × G => -((f : G → R) q.1 * (u : G → R) q.2)) (σ, τ, ρ)
      = cupFun12 (f : G → R) (((g - g' : Z2 G R)) : Cochain2 G R) (σ, τ, ρ)
  simp only [cupFun12, d2Fun_apply, d1Fun_apply, htriv]
  rw [hcoe' τ ρ, hcoc]
  simp only [d1Fun_apply, htriv]
  ring

/-- **The cup product on cohomology**, `H¹(G,R) × H²(G,R) → H³(G,R)`, for a trivial action: the
cup product of any two representatives (well defined by the two lemmas above). -/
noncomputable def cupH1H2 (htriv : ∀ (σ : G) (r : R), σ • r = r) (x : H1 G R) (y : H2 G R) :
    H3 G R :=
  H3.mk (cupZ1Z2 htriv (Quotient.out x) (Quotient.out y))

/-- The defining property of `cupH1H2` on representatives. -/
theorem cupH1H2_mk (htriv : ∀ (σ : G) (r : R), σ • r = r) (f : Z1 G R) (g : Z2 G R) :
    cupH1H2 htriv (H1.mk f) (H2.mk g) = H3.mk (cupZ1Z2 htriv f g) := by
  unfold cupH1H2
  have hf : H1.mk (Quotient.out (H1.mk f)) = H1.mk f := Quotient.out_eq (H1.mk f)
  have hg : H2.mk (Quotient.out (H2.mk g)) = H2.mk g := Quotient.out_eq (H2.mk g)
  have h₁ : H3.mk (cupZ1Z2 htriv (Quotient.out (H1.mk f)) (Quotient.out (H2.mk g)))
      = H3.mk (cupZ1Z2 htriv f (Quotient.out (H2.mk g))) :=
    (cupZ1Z2_mk_eq_of_mk_eq_left htriv hf.symm _).symm
  have h₂ : H3.mk (cupZ1Z2 htriv f (Quotient.out (H2.mk g))) = H3.mk (cupZ1Z2 htriv f g) :=
    (cupZ1Z2_mk_eq_of_mk_eq_right htriv f hg.symm).symm
  exact h₁.trans h₂

/-- **Linearity of the cup product on cohomology in the left variable.** -/
theorem cupH1H2_add_left (htriv : ∀ (σ : G) (r : R), σ • r = r) (x x' : H1 G R) (y : H2 G R) :
    cupH1H2 htriv (x + x') y = cupH1H2 htriv x y + cupH1H2 htriv x' y := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  obtain ⟨f', rfl⟩ := Quotient.exists_rep x'
  obtain ⟨g, rfl⟩ := Quotient.exists_rep y
  show cupH1H2 htriv (H1.mk f + H1.mk f') (H2.mk g)
      = cupH1H2 htriv (H1.mk f) (H2.mk g) + cupH1H2 htriv (H1.mk f') (H2.mk g)
  rw [← H1_mk_add, cupH1H2_mk, cupH1H2_mk, cupH1H2_mk, cupZ1Z2_add_left, H3_mk_add]

/-- **Linearity of the cup product on cohomology in the right variable.** -/
theorem cupH1H2_add_right (htriv : ∀ (σ : G) (r : R), σ • r = r) (x : H1 G R) (y y' : H2 G R) :
    cupH1H2 htriv x (y + y') = cupH1H2 htriv x y + cupH1H2 htriv x y' := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  obtain ⟨g, rfl⟩ := Quotient.exists_rep y
  obtain ⟨g', rfl⟩ := Quotient.exists_rep y'
  show cupH1H2 htriv (H1.mk f) (H2.mk g + H2.mk g')
      = cupH1H2 htriv (H1.mk f) (H2.mk g) + cupH1H2 htriv (H1.mk f) (H2.mk g')
  rw [← H2_mk_add, cupH1H2_mk, cupH1H2_mk, cupH1H2_mk, cupZ1Z2_add_right, H3_mk_add]

end Work.ShafarevichKoch
