/-
Copyright: the martinet_totally_real_towers team.

# The connecting homomorphism `H²(G,C) → H³(G,A)` of a coefficient short exact sequence

This module completes the long exact sequence of a short exact sequence
`0 → A → B → C → 0` of discrete `G`-modules (`Work.ConCohomology.CoeffSES`) one degree beyond
`Work.ConCohomology.connecting1`: the connecting map

```
δ² : H²(G,C) →+ H³(G,A)
```

of `Submission/Work/ShafarevichKoch/Cohomology3.lean`'s degree `3`, which is the map appearing in
the `ℤ`-power sequence of Hajir--Maire--Ramakrishna (`0 → H²(G,ℤ)/p → H²(G,ℤ/p) → H³(G,ℤ)[p] → 0`)
used for the Shafarevich--Koch relation bound.

The construction follows `Connecting.lean`'s pattern for `δ¹`, one degree up:

* for a lift `u : C²(G,B)` of a `2`-cocycle `z : Z²(G,C)`, the cochain `d²u` takes values in
  `ker g = im f` (`g` is equivariant and additive and `z` is a cocycle), so
  `w := S.invFun ∘ d²u` is a well defined `A`-valued `3`-cochain with `f (w p) = d²u p`;
* `w` is a `3`-cocycle because `f (d³w p) = d³(d²u) p = 0` (`d3Fun_d2Fun`, `d3Fun_comp`) and `f`
  is injective -- the inverse `S.invFun` is not additive, so the argument never expands `d³w`;
* two lifts of the same cocycle differ by a cochain with values in `im f`, and the corresponding
  `w`'s differ by an honest `3`-coboundary `d²(S.invFun ∘ (u₁ - u₂))`; this is what makes the
  construction independent of the lift, and (applied to `u₁ = u₀(z₁+z₂)` and
  `u₂ = u₀z₁ + u₀z₂`) additive;
* finally the map on `Z²` vanishes on `2`-coboundaries, so it descends to `H²(G,C)`.

## Main declarations

* `Work.ShafarevichKoch.connFun3`, `connCochain3`, `connCocycle3`, `connFun3_eq_add`;
* `Work.ShafarevichKoch.canonU2`, `psiZ`, `psiZ_add`, `psiZ_eq_zero_of_mem_B2`;
* `Work.ShafarevichKoch.connecting2` : `∃ δ : H²(G,C) →+ H³(G,A)` whose value on the class of a
  `2`-cocycle `z` is computed by the connecting cocycle of *every* lift `u` of `z`, as stated.
-/

import Mathlib
import Submission.Work.ShafarevichKoch.Cohomology3Map

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
variable [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]

/-! ## Naturality of `d²` under an equivariant coefficient map -/

lemma d2Fun_eqHom_comp (F : EqHom G A B) (f : G × G → A) :
    d2Fun (G := G) (M := B) (fun p => F (f p)) =
      fun p => F (d2Fun (G := G) (M := A) f p) := by
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [d2Fun_apply, EqHom.map_add, EqHom.map_sub, EqHom.map_smul]

/-! ## Elementary facts about `S.invFun` -/

lemma f_invFun_of_g_eq_zero (S : CoeffSES G A B C) {b : B} (hb : S.g b = 0) :
    S.f (S.invFun b) = b :=
  f_invFun_of_exists S ((S.exact b).mp hb)

lemma invFun_add_of_g_eq_zero (S : CoeffSES G A B C) {b₁ b₂ : B}
    (h₁ : S.g b₁ = 0) (h₂ : S.g b₂ = 0) :
    S.invFun (b₁ + b₂) = S.invFun b₁ + S.invFun b₂ :=
  invFun_add S ((S.exact b₁).mp h₁) ((S.exact b₂).mp h₂)

lemma invFun_zero (S : CoeffSES G A B C) : S.invFun 0 = 0 :=
  invFun_eq_of S (EqHom.map_zero S.f)

@[simp] lemma invFun_f_apply (S : CoeffSES G A B C) (a : A) : S.invFun (S.f a) = a :=
  invFun_eq_of S rfl

/-! ## The section of `g` and the raw connecting cochain in degree `2 → 3` -/

/-- The chosen set-theoretic section of `g`, applied pointwise to a `2`-cochain. -/
def coeffSect2 (S : CoeffSES G A B C) (c : Cochain2 G C) : Cochain2 G B :=
  ⟨fun p => S.sect (c p), c.isLocallyConstant.comp S.sect⟩

@[simp] lemma coeffSect2_apply (S : CoeffSES G A B C) (c : Cochain2 G C) (p : G × G) :
    coeffSect2 S c p = S.sect (c p) := rfl

lemma g_coeffSect2 (S : CoeffSES G A B C) (c : Cochain2 G C) (p : G × G) :
    S.g (coeffSect2 S c p) = c p := S.g_sect (c p)

/-- `S.invFun` applied pointwise to a `2`-cochain with values in the image of `f`. -/
def coeffInvFun2 (S : CoeffSES G A B C) (v : Cochain2 G B) : Cochain2 G A :=
  ⟨fun p => S.invFun (v p), v.isLocallyConstant.comp S.invFun⟩

@[simp] lemma coeffInvFun2_apply (S : CoeffSES G A B C) (v : Cochain2 G B) (p : G × G) :
    coeffInvFun2 S v p = S.invFun (v p) := rfl

/-- The raw degree `2 → 3` connecting cochain `S.invFun ∘ d²u` attached to a `2`-cochain `u`. -/
def connFun3 (S : CoeffSES G A B C) (u : Cochain2 G B) : G × G × G → A :=
  fun p => S.invFun (d2Fun (u : G × G → B) p)

@[simp] lemma connFun3_apply (S : CoeffSES G A B C) (u : Cochain2 G B) (p : G × G × G) :
    connFun3 S u p = S.invFun (d2Fun (u : G × G → B) p) := rfl

lemma isLocallyConstant_connFun3 (S : CoeffSES G A B C) (u : Cochain2 G B) :
    IsLocallyConstant (connFun3 S u) :=
  (isLocallyConstant_d2Fun u).comp S.invFun

def connCochain3 (S : CoeffSES G A B C) (u : Cochain2 G B) : Cochain3 G A :=
  ⟨connFun3 S u, isLocallyConstant_connFun3 S u⟩

@[simp] lemma connCochain3_apply (S : CoeffSES G A B C) (u : Cochain2 G B) (p : G × G × G) :
    connCochain3 S u p = S.invFun (d2Fun (u : G × G → B) p) := rfl

/-! ## The connecting cochain is a `3`-cocycle -/

/-- If `u` is a lift of a `2`-cocycle `z`, then `g` kills `d²u`. -/
lemma g_d2Fun_of_lift (S : CoeffSES G A B C) {u : Cochain2 G B} {z : Z2 G C}
    (h : ∀ p, S.g (u p) = (z : Cochain2 G C) p) (p : G × G × G) :
    S.g (d2Fun (u : G × G → B) p) = 0 := by
  have hnat := congrFun (d2Fun_eqHom_comp (G := G) S.g (u : G × G → B)) p
  have hz : d2Fun (G := G) (M := C) ((z : Z2 G C) : G × G → C) = 0 :=
    (isCocycle2_iff_d2Fun _).mp (mem_Z2.mp z.2)
  rw [← hnat]
  rw [show (fun q => S.g (u q)) = ((z : Z2 G C) : Cochain2 G C) from funext h]
  rw [hz]
  rfl

/-- `f` inverts the connecting cochain: `f (S.invFun (d²u p)) = d²u p`. -/
lemma f_connFun3 (S : CoeffSES G A B C) {u : Cochain2 G B} {z : Z2 G C}
    (h : ∀ p, S.g (u p) = (z : Cochain2 G C) p) (p : G × G × G) :
    S.f (connFun3 S u p) = d2Fun (u : G × G → B) p :=
  f_invFun_of_g_eq_zero S (g_d2Fun_of_lift S h p)

/-- `S.invFun ∘ d²u` is a `3`-cocycle whenever `u` is a lift of a `2`-cocycle `z`. -/
lemma d3Fun_connFun3_eq_zero (S : CoeffSES G A B C) {u : Cochain2 G B} {z : Z2 G C}
    (h : ∀ p, S.g (u p) = (z : Cochain2 G C) p) (p : G × G × G × G) :
    d3Fun (connFun3 S u) p = 0 := by
  obtain ⟨σ, τ, ρ, υ⟩ := p
  apply S.injective_f
  rw [EqHom.map_zero]
  have hcomp := congrFun (d3Fun_comp (G := G) S.f (connFun3 S u)) (σ, τ, ρ, υ)
  rw [← hcomp]
  rw [show (fun q => S.f (connFun3 S u q)) = d2Fun (G := G) (M := B) (u : G × G → B) from
    funext (f_connFun3 S h)]
  rw [d3Fun_d2Fun]
  rfl

/-- The `3`-cocycle `S.invFun ∘ d²u` attached to a lift `u` of the `2`-cocycle `z`. -/
def connCocycle3 (S : CoeffSES G A B C) (u : Cochain2 G B) (z : Z2 G C)
    (h : ∀ p, S.g (u p) = (z : Cochain2 G C) p) : Z3 G A :=
  ⟨connCochain3 S u, by
    rw [mem_Z3]
    ext p
    obtain ⟨σ, τ, ρ, υ⟩ := p
    show d3Fun (G := G) (M := A) (connFun3 S u) (σ, τ, ρ, υ) = 0
    exact d3Fun_connFun3_eq_zero S h (σ, τ, ρ, υ)⟩

@[simp] lemma connCocycle3_coe (S : CoeffSES G A B C) (u : Cochain2 G B) (z : Z2 G C)
    (h : ∀ p, S.g (u p) = (z : Cochain2 G C) p) :
    ((connCocycle3 S u z h : Z3 G A) : Cochain3 G A) = connCochain3 S u := rfl

/-! ## The fundamental computation: comparing two lifts of the same cocycle -/

/-- **The key computation.**  If `u₂` is a lift of the `2`-cocycle `z` and the difference
`u₁ - u₂` has values in `ker g = im f`, then the connecting cochains `invFun ∘ d²u₁` and
`invFun ∘ d²u₂` differ by the `3`-coboundary `d²` of the `A`-valued cochain
`invFun ∘ (u₁ - u₂)`. -/
lemma connFun3_eq_add (S : CoeffSES G A B C) {u₁ u₂ : Cochain2 G B} {z : Z2 G C}
    (h₂ : ∀ p, S.g (u₂ p) = (z : Cochain2 G C) p)
    (h : ∀ p, S.g ((u₁ - u₂) p) = 0) :
    connFun3 S u₁ = connFun3 S u₂ + d2Fun (G := G) (M := A)
      ((coeffInvFun2 S (u₁ - u₂) : Cochain2 G A) : G × G → A) := by
  -- `f` inverts `S.invFun` on the difference cochain
  have hV : (fun q : G × G => S.f ((coeffInvFun2 S (u₁ - u₂) : Cochain2 G A) q))
      = ((u₁ - u₂ : Cochain2 G B) : G × G → B) := by
    funext q
    exact f_invFun_of_g_eq_zero S (h q)
  -- hence `d²(u₁ - u₂) = f ∘ d²(invFun ∘ (u₁ - u₂))`
  have hd2 : d2Fun (G := G) (M := B) ((u₁ - u₂ : Cochain2 G B) : G × G → B)
      = fun q => S.f (d2Fun (G := G) (M := A)
          ((coeffInvFun2 S (u₁ - u₂) : Cochain2 G A) : G × G → A) q) := by
    rw [← hV]
    exact d2Fun_eqHom_comp (G := G) S.f
      ((coeffInvFun2 S (u₁ - u₂) : Cochain2 G A) : G × G → A)
  -- decompose `u₁ = u₂ + (u₁ - u₂)`
  have hsplit : ((u₁ : G × G → B))
      = ((u₂ : G × G → B)) + ((u₁ - u₂ : Cochain2 G B) : G × G → B) := by
    funext q
    simp only [Pi.add_apply, LocallyConstant.coe_sub, Pi.sub_apply]
    abel
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  have hmain : d2Fun (G := G) (M := B) (u₁ : G × G → B) (σ, τ, ρ)
      = d2Fun (G := G) (M := B) (u₂ : G × G → B) (σ, τ, ρ)
        + S.f (d2Fun (G := G) (M := A)
            ((coeffInvFun2 S (u₁ - u₂) : Cochain2 G A) : G × G → A) (σ, τ, ρ)) := by
    rw [hsplit, d2Fun_add]
    simp only [Pi.add_apply]
    rw [congrFun hd2 (σ, τ, ρ)]
  have e₁ : ∃ a : A, S.f a = d2Fun (G := G) (M := B) (u₂ : G × G → B) (σ, τ, ρ) :=
    ⟨connFun3 S u₂ (σ, τ, ρ), f_connFun3 S h₂ (σ, τ, ρ)⟩
  have e₂ : ∃ a : A, S.f a = S.f (d2Fun (G := G) (M := A)
      ((coeffInvFun2 S (u₁ - u₂) : Cochain2 G A) : G × G → A) (σ, τ, ρ)) :=
    ⟨_, rfl⟩
  show S.invFun (d2Fun (G := G) (M := B) (u₁ : G × G → B) (σ, τ, ρ))
      = S.invFun (d2Fun (G := G) (M := B) (u₂ : G × G → B) (σ, τ, ρ))
        + d2Fun (G := G) (M := A)
            ((coeffInvFun2 S (u₁ - u₂) : Cochain2 G A) : G × G → A) (σ, τ, ρ)
  rw [hmain, invFun_add S e₁ e₂, invFun_f_apply]

/-! ## The connecting map on the level of cocycles -/

@[simp] lemma H3.mk_add (a b : Z3 G A) : H3.mk (a + b) = H3.mk a + H3.mk b :=
  (QuotientAddGroup.mk_add (B3' G A) a b).symm

lemma H3.mk_eq_zero_iff (a : Z3 G A) : H3.mk a = 0 ↔ a ∈ B3' G A :=
  QuotientAddGroup.eq_zero_iff a

/-- Two lifts of the same `2`-cocycle give the same class in `H³(G,A)`. -/
lemma mk_connCocycle3_eq (S : CoeffSES G A B C) {u₁ u₂ : Cochain2 G B} {z : Z2 G C}
    (h₁ : ∀ p, S.g (u₁ p) = (z : Cochain2 G C) p)
    (h₂ : ∀ p, S.g (u₂ p) = (z : Cochain2 G C) p) :
    H3.mk (connCocycle3 S u₁ z h₁) = H3.mk (connCocycle3 S u₂ z h₂) := by
  rw [H3.mk_eq_mk_iff, mem_B3', B3, AddMonoidHom.mem_range]
  refine ⟨coeffInvFun2 S (u₁ - u₂), ?_⟩
  have hV : ∀ q : G × G, S.g ((u₁ - u₂) q) = 0 := by
    intro q
    simp only [LocallyConstant.coe_sub, Pi.sub_apply, EqHom.map_sub, h₁ q, h₂ q, sub_self]
  have hfun := connFun3_eq_add (S := S) h₂ hV
  ext p
  obtain ⟨σ, τ, ρ⟩ := p
  show d2Fun (G := G) (M := A) ((coeffInvFun2 S (u₁ - u₂) : Cochain2 G A) : G × G → A)
      (σ, τ, ρ) = connFun3 S u₁ (σ, τ, ρ) - connFun3 S u₂ (σ, τ, ρ)
  have hp := congrFun hfun (σ, τ, ρ)
  simp only [Pi.add_apply] at hp
  rw [hp]
  abel

/-! ## Additivity and the canonical connecting map on `Z²` -/

/-- The connecting cochain is additive in the lift. -/
lemma connFun3_add (S : CoeffSES G A B C) {u u' : Cochain2 G B} {z z' : Z2 G C}
    (h : ∀ p, S.g (u p) = (z : Cochain2 G C) p)
    (h' : ∀ p, S.g (u' p) = (z' : Cochain2 G C) p) :
    connFun3 S (u + u') = connFun3 S u + connFun3 S u' := by
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  have hd : d2Fun (G := G) (M := B) ((u + u' : Cochain2 G B) : G × G → B) (σ, τ, ρ)
      = d2Fun (G := G) (M := B) (u : G × G → B) (σ, τ, ρ)
        + d2Fun (G := G) (M := B) (u' : G × G → B) (σ, τ, ρ) := by
    rw [LocallyConstant.coe_add, d2Fun_add]
    rfl
  show S.invFun (d2Fun (G := G) (M := B) ((u + u' : Cochain2 G B) : G × G → B) (σ, τ, ρ))
      = S.invFun (d2Fun (G := G) (M := B) (u : G × G → B) (σ, τ, ρ))
        + S.invFun (d2Fun (G := G) (M := B) (u' : G × G → B) (σ, τ, ρ))
  rw [hd, invFun_add S ⟨connFun3 S u (σ, τ, ρ), f_connFun3 S h (σ, τ, ρ)⟩
    ⟨connFun3 S u' (σ, τ, ρ), f_connFun3 S h' (σ, τ, ρ)⟩]

/-- The classes of the connecting cocycles are additive in the lifts. -/
lemma mk_connCocycle3_add (S : CoeffSES G A B C) {u u' : Cochain2 G B} {z z' : Z2 G C}
    (h : ∀ p, S.g (u p) = (z : Cochain2 G C) p)
    (h' : ∀ p, S.g (u' p) = (z' : Cochain2 G C) p)
    (hsum : ∀ p, S.g ((u + u') p) = ((z + z' : Z2 G C) : Cochain2 G C) p) :
    H3.mk (connCocycle3 S (u + u') (z + z') hsum)
      = H3.mk (connCocycle3 S u z h) + H3.mk (connCocycle3 S u' z' h') := by
  rw [← H3.mk_add]
  congr 1
  refine Subtype.ext ?_
  rw [AddSubgroup.coe_add, connCocycle3_coe, connCocycle3_coe, connCocycle3_coe]
  show connCochain3 S (u + u') = connCochain3 S u + connCochain3 S u'
  ext p
  obtain ⟨σ, τ, ρ⟩ := p
  have hp := congrFun (connFun3_add (S := S) h h') (σ, τ, ρ)
  simp only [Pi.add_apply] at hp
  simpa only [connCochain3_apply, connFun3_apply, LocallyConstant.coe_add, Pi.add_apply] using hp

/-- The canonical lift of a `2`-cocycle along the section of `g`. -/
def canonU2 (S : CoeffSES G A B C) (z : Z2 G C) : Cochain2 G B :=
  coeffSect2 S (z : Cochain2 G C)

lemma g_canonU2 (S : CoeffSES G A B C) (z : Z2 G C) (p : G × G) :
    S.g (canonU2 S z p) = (z : Cochain2 G C) p := S.g_sect ((z : Cochain2 G C) p)

/-- The connecting map `Z²(G,C) → H³(G,A)`, computed with the canonical lift. -/
def psiZ (S : CoeffSES G A B C) (z : Z2 G C) : H3 G A :=
  H3.mk (connCocycle3 S (canonU2 S z) z (g_canonU2 S z))

lemma psiZ_add (S : CoeffSES G A B C) (z₁ z₂ : Z2 G C) :
    psiZ S (z₁ + z₂) = psiZ S z₁ + psiZ S z₂ := by
  have hsum : ∀ p : G × G, S.g ((canonU2 S z₁ + canonU2 S z₂) p)
      = ((z₁ + z₂ : Z2 G C) : Cochain2 G C) p := by
    intro p
    simp only [LocallyConstant.coe_add, Pi.add_apply, EqHom.map_add, g_canonU2,
      AddSubgroup.coe_add]
  have hA := mk_connCocycle3_eq (S := S) (z := z₁ + z₂) (g_canonU2 S (z₁ + z₂)) hsum
  have hB := mk_connCocycle3_add (S := S) (z := z₁) (z' := z₂)
    (g_canonU2 S z₁) (g_canonU2 S z₂) hsum
  show H3.mk (connCocycle3 S (canonU2 S (z₁ + z₂)) (z₁ + z₂) (g_canonU2 S (z₁ + z₂)))
      = H3.mk (connCocycle3 S (canonU2 S z₁) z₁ (g_canonU2 S z₁))
        + H3.mk (connCocycle3 S (canonU2 S z₂) z₂ (g_canonU2 S z₂))
  exact hA.trans hB

/-- The connecting map on `Z²` vanishes on `2`-coboundaries, so it descends to `H²`. -/
lemma psiZ_eq_zero_of_mem_B2 (S : CoeffSES G A B C) {z : Z2 G C} (hz : z ∈ B2' G C) :
    psiZ S z = 0 := by
  rw [mem_B2', B2, AddMonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  -- pointwise form of `d¹c = z`
  have hc' : ∀ σ τ : G, d1Fun (G := G) (M := C) (c : G → C) (σ, τ)
      = (z : Cochain2 G C) (σ, τ) := by
    intro σ τ
    have h := congrFun (congrArg (fun w : Cochain2 G C => (w : G × G → C)) hc) (σ, τ)
    simpa [d1Hom] using h
  -- a lift of `c` to `B`
  let cB : Cochain1 G B := ⟨fun σ => S.sect (c σ), c.isLocallyConstant.comp S.sect⟩
  have gcB : ∀ σ : G, S.g (cB σ) = c σ := fun σ => S.g_sect (c σ)
  have hu' : ∀ p : G × G, S.g ((d1Hom G B cB) p) = (z : Cochain2 G C) p := by
    intro p
    obtain ⟨σ, τ⟩ := p
    calc S.g ((d1Hom G B cB) (σ, τ))
        = d1Fun (G := G) (M := C) (c : G → C) (σ, τ) := by
          simp only [d1Hom_apply, EqHom.map_add, EqHom.map_sub, EqHom.map_smul, gcB]
          rfl
      _ = (z : Cochain2 G C) (σ, τ) := hc' σ τ
  have hV : ∀ p : G × G, S.g ((canonU2 S z - d1Hom G B cB) p) = 0 := by
    intro p
    simp only [LocallyConstant.coe_sub, Pi.sub_apply, EqHom.map_sub, g_canonU2, hu' p, sub_self]
  have hfun := connFun3_eq_add (S := S) (u₁ := canonU2 S z) (u₂ := d1Hom G B cB) (z := z) hu' hV
  have hzero : connFun3 S (d1Hom G B cB) = 0 := by
    funext p
    obtain ⟨σ, τ, ρ⟩ := p
    show S.invFun (d2Fun (G := G) (M := B) ((d1Hom G B cB) : G × G → B) (σ, τ, ρ)) = 0
    rw [show d2Fun (G := G) (M := B) ((d1Hom G B cB) : G × G → B) = 0 from ?_]
    · exact invFun_zero S
    · show d2Fun (G := G) (M := B) (d1Fun (G := G) (M := B) (cB : G → B)) = 0
      exact d2Fun_d1Fun (cB : G → B)
  rw [psiZ, H3.mk_eq_zero_iff, mem_B3', B3, AddMonoidHom.mem_range]
  refine ⟨coeffInvFun2 S (canonU2 S z - d1Hom G B cB), ?_⟩
  rw [connCocycle3_coe]
  ext p
  obtain ⟨σ, τ, ρ⟩ := p
  show d2Fun (G := G) (M := A)
        ((coeffInvFun2 S (canonU2 S z - d1Hom G B cB) : Cochain2 G A) : G × G → A) (σ, τ, ρ)
      = connFun3 S (canonU2 S z) (σ, τ, ρ)
  have hp := congrFun hfun (σ, τ, ρ)
  simp only [Pi.add_apply] at hp
  rw [hp, congrFun hzero (σ, τ, ρ)]
  simp

theorem connecting2 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [Work.ConCohomology.IsDiscreteGModule G A] [Work.ConCohomology.IsDiscreteGModule G B]
    [Work.ConCohomology.IsDiscreteGModule G C]
    (S : Work.ConCohomology.CoeffSES G A B C) :
    ∃ δ : Work.ConCohomology.H2 G C →+ Work.ShafarevichKoch.H3 G A,
      ∀ (z : Work.ConCohomology.Z2 G C) (u : Work.ConCohomology.Cochain2 G B),
        (∀ p : G × G, S.g (u p) = (z : Work.ConCohomology.Cochain2 G C) p) →
        ∃ w : Work.ShafarevichKoch.Z3 G A,
          Work.ShafarevichKoch.H3.mk w = δ (Work.ConCohomology.H2.mk z) ∧
          (∀ p : G × G × G,
            S.f ((w : G × G × G → A) p) = Work.ConCohomology.d2Fun (u : G × G → B) p) := by
  -- The additive homomorphism `Z²(G,C) → H³(G,A)` given by the raw connecting cochain.
  have hψ_add : ∀ z₁ z₂ : Z2 G C, psiZ S (z₁ + z₂) = psiZ S z₁ + psiZ S z₂ := psiZ_add S
  let psi : Z2 G C →+ H3 G A := AddMonoidHom.mk' (psiZ S) hψ_add
  have hpsi : ∀ z : Z2 G C, psi z = psiZ S z := fun z => rfl
  -- It kills `2`-coboundaries, so it descends to `H²`.
  have hker : B2' G C ≤ psi.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker, hpsi z]
    exact psiZ_eq_zero_of_mem_B2 S hz
  refine ⟨QuotientAddGroup.lift (B2' G C) psi hker, ?_⟩
  intro z u hu
  refine ⟨connCocycle3 S u z hu, ?_, ?_⟩
  · -- the class of the connecting cocycle of *any* lift is `δ` of the class of `z`
    have hδ : QuotientAddGroup.lift (B2' G C) psi hker (H2.mk z) = psiZ S z := by
      show QuotientAddGroup.lift (B2' G C) psi hker (QuotientAddGroup.mk z) = psiZ S z
      rw [QuotientAddGroup.lift_mk]
      rfl
    rw [hδ]
    exact mk_connCocycle3_eq (S := S) hu (g_canonU2 S z)
  · intro p
    exact f_connFun3 S hu p

end Work.ShafarevichKoch
