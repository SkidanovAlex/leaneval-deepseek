/-
Copyright: the martinet_totally_real_towers team.

# Exactness of the long exact cohomology sequence at `H²(G,B)`

For a short exact sequence `0 → A → B → C → 0` of discrete `G`-modules (with `G` a topological
group acting continuously on the discrete coefficient groups), the induced sequence

`H²(G,A) --H²(f)--> H²(G,B) --H²(g)--> H²(G,C)`

is exact at `H²(G,B)`:

`H²Map S.g x = 0 ↔ ∃ y : H²(G,A), H²Map S.f y = x`.

This is the diagram chase attached to the short exact sequence of cochain complexes
`0 → C¹(G,A) → C¹(G,B) → C¹(G,C) → 0` (which is degreewise exact, since `A → B → C` is exact and
a locally constant cochain with values in the kernel of `g` lifts along any set-theoretic section
of `g`, remaining locally constant).

* **Image contained in the kernel**: `g ∘ f = 0`, because `f` lands in the kernel of `g`.
* **Kernel contained in the image**: given a `2`-cocycle `z` in `B` whose class dies in `H²(G,C)`,
  there is a `1`-cochain `u` in `C` with `d¹u = g z`; lift `u` to a `1`-cochain `ũ` in `B` along the
  section `S.sect` of `g`; then `ζ = z - d¹ũ` is a `2`-cocycle of `B` killed by `g`, hence is the
  image under `S.f` of a locally constant `2`-cochain `w` of `A` (pointwise inverting `f` by
  `S.invFun`); `w` is a `2`-cocycle because `S.f` is injective in degree `3`; and, finally,
  `z = S.f w + d¹ũ`, so the class of `z` is the image of the class of `w`.
-/

import Mathlib
import Submission.Work.ConCohomology.Connecting

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

private lemma CoeffSES.g_apply_f_eq_zero {G : Type*} [Group G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (S : CoeffSES G A B C) (a : A) : S.g (S.f a) = 0 :=
  (S.exact (S.f a)).mpr ⟨a, rfl⟩

/-- If `g b = 0`, then the chosen set-theoretic inverse `S.invFun` of `f` really inverts `f`
at `b`. -/
private lemma CoeffSES.f_invFun_eq_of_g_eq_zero_aux {G : Type*} [Group G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (S : CoeffSES G A B C) {b : B} (hb : S.g b = 0) : S.f (S.invFun b) = b := by
  have hex : ∃ a : A, S.f a = b := (S.exact b).mp hb
  simp only [CoeffSES.invFun_eq, hex, dite_true]
  exact Classical.choose_spec hex

/-- The second differential is additive on differences of functions. -/
private lemma d2Fun_sub' {G : Type*} [Group G] [TopologicalSpace G] {B : Type*}
    [AddCommGroup B] [DistribMulAction G B] (f g : G × G → B) :
    d2Fun (f - g) = d2Fun f - d2Fun g := by
  rw [sub_eq_add_neg, d2Fun_add, d2Fun_neg, sub_eq_add_neg]

lemma exact_H2_B {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (x : H2 G B) :
    H2Map S.g x = 0 ↔ ∃ y : H2 G A, H2Map S.f y = x := by
  constructor
  · -- The class of `z` dies under `H²(g)`.
    intro h
    revert h
    refine QuotientAddGroup.induction_on x ?_
    intro z hz
    change (H2Map S.g) (H2.mk z) = 0 at hz
    change ∃ y : H2 G A, H2Map S.f y = H2.mk z
    rw [H2Map_mk, H2.mk_eq_zero_iff, mem_B2'] at hz
    obtain ⟨u, hu⟩ := hz
    -- `u` is a `1`-cochain of `C` with `d¹u = g z`; lift it to a `1`-cochain of `B`.
    let uB : Cochain1 G B := ⟨fun σ => S.sect (u σ), u.isLocallyConstant.comp S.sect⟩
    have hgu : cochain1Map S.g uB = u := by
      refine LocallyConstant.ext fun σ => ?_
      simp only [cochain1Map_apply]
      exact S.g_sect (u σ)
    -- The coboundary `d¹uB` as an element of `Z²(G,B)`.
    let zu : Z2 G B := ⟨d1Hom G B uB, by
      rw [mem_Z2, isCocycle2_iff_d2Fun]
      exact d2Fun_d1Fun (uB : G → B)⟩
    have hzu : zu ∈ B2' G B := by
      rw [mem_B2']
      exact ⟨uB, rfl⟩
    -- The `C`-value of the difference `z - d¹uB` is zero.
    have hgζ : ∀ p : G × G,
        S.g ((z : Cochain2 G B) p - ((d1Hom G B uB : Cochain2 G B)) p) = 0 := by
      intro p
      have h1 : S.g ((z : Cochain2 G B) p)
          = (((Z2Map S.g z : Z2 G C)) : Cochain2 G C) p := by
        rw [Z2Map_coe]
        rfl
      have h2 : S.g (((d1Hom G B uB : Cochain2 G B)) p)
          = (((d1Hom G C u : Cochain2 G C)) p) := by
        rw [← hgu, d1Hom_cochain1Map]
        rfl
      rw [EqHom.map_sub, h1, h2, hu]
      abel
    have harm : IsLocallyConstant fun p : G × G =>
        (z : Cochain2 G B) p - ((d1Hom G B uB : Cochain2 G B)) p :=
      (z.1.isLocallyConstant).sub ((d1Hom G B uB).isLocallyConstant)
    -- The lift `w` of `z - d¹uB` to `A`, pointwise along `S.invFun`.
    let w : Cochain2 G A :=
      ⟨fun p => S.invFun ((z : Cochain2 G B) p - ((d1Hom G B uB : Cochain2 G B)) p),
        harm.comp S.invFun⟩
    have hfw : ∀ p : G × G,
        S.f (w p) = (z : Cochain2 G B) p - ((d1Hom G B uB : Cochain2 G B)) p := by
      intro p
      have hex : ∃ a : A, S.f a = (z : Cochain2 G B) p - ((d1Hom G B uB : Cochain2 G B)) p :=
        (S.exact _).mp (hgζ p)
      show S.f (S.invFun ((z : Cochain2 G B) p - ((d1Hom G B uB : Cochain2 G B)) p)) = _
      simp only [CoeffSES.invFun_eq, hex, dite_true]
      exact Classical.choose_spec hex
    -- `w` is a `2`-cocycle, because `f` is injective in degree `3` and `z - d¹uB` is a cocycle.
    have hd2w : d2Fun (w : G × G → A) = 0 := by
      have hz0 : d2Fun (fun q : G × G => (z : Cochain2 G B) q) = 0 :=
        (isCocycle2_iff_d2Fun (fun q : G × G => (z : Cochain2 G B) q)).mp (mem_Z2.mp z.2)
      have hd1uB0 : d2Fun (d1Fun (uB : G → B)) = 0 := d2Fun_d1Fun (uB : G → B)
      have hfun : (fun q : G × G => S.f (w q))
          = (fun q : G × G => (z : Cochain2 G B) q) - d1Fun (uB : G → B) := by
        funext q
        rw [hfw q]
        rfl
      funext p
      apply S.injective_f
      simp only [Pi.zero_apply, EqHom.map_zero]
      have key : S.f (d2Fun (w : G × G → A) p)
          = d2Fun (fun q : G × G => S.f (w q)) p := by
        rw [d2Fun_comp]
      rw [key, hfun, d2Fun_sub']
      simp only [Pi.sub_apply, hz0, hd1uB0, Pi.zero_apply, sub_zero]
    have hwZ : w ∈ Z2 G A := by
      rw [mem_Z2, isCocycle2_iff_d2Fun]
      exact hd2w
    let wZ : Z2 G A := ⟨w, hwZ⟩
    refine ⟨H2.mk wZ, ?_⟩
    rw [H2Map_mk]
    have hcomp : ((Z2Map S.f wZ : Z2 G B) : Cochain2 G B)
        = (z : Cochain2 G B) - (d1Hom G B uB : Cochain2 G B) := by
      refine LocallyConstant.ext fun p => ?_
      simp only [Z2Map_coe, cochain2Map_apply]
      exact hfw p
    have hZeq : Z2Map S.f wZ = z - zu := by
      apply Subtype.ext
      rw [hcomp]
      rfl
    rw [hZeq]
    refine (H2.mk_eq_mk_iff _ _).mpr ?_
    rw [mem_B2']
    have hmem : (z - zu) - z = -zu := by abel
    rw [hmem]
    exact neg_mem hzu
  · -- The image of `H²(f)` is contained in the kernel of `H²(g)`, since `g ∘ f = 0`.
    rintro ⟨y, rfl⟩
    refine QuotientAddGroup.induction_on y ?_
    intro a
    change (H2Map S.g) ((H2Map S.f) (H2.mk a)) = 0
    rw [H2Map_mk, H2Map_mk, H2.mk_eq_zero_iff, mem_B2']
    have hzero : ((Z2Map S.g (Z2Map S.f a) : Z2 G C) : Cochain2 G C) = 0 := by
      refine LocallyConstant.ext fun p => ?_
      obtain ⟨σ, τ⟩ := p
      simp only [Z2Map_coe, cochain2Map_apply]
      exact (S.exact (S.f ((a : Cochain2 G A) (σ, τ)))).mpr
        ⟨(a : Cochain2 G A) (σ, τ), rfl⟩
    rw [hzero]
    exact AddSubgroup.zero_mem _


end Work.ConCohomology
