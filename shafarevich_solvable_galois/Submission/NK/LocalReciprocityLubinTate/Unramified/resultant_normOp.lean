import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormOp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The resultant identity `Res_Y(h, R_f(g)) = Res_X(h ∘ f, g)` for the norm operator

For a commutative ring `A` and polynomials `f, h, g ∈ A[X]` with `f` and `h` monic and
`0 < deg f`, the norm operator `normOp f g = Res_X(f(X) - Y, g(X)) ∈ A[Y]` satisfies

`Res_Y(h(Y), normOp f g) = Res_X(h(f(X)), g(X))`.

This is the "norm of the norm is the norm" identity: `normOp f g` is the norm of `g` along the
degree-`deg f` algebra `A[Y][X]/(f(X)-Y)`, and `Res_Y(h, ·)` is the norm along `A[Y]/(h)`; the two
compose into the norm along `A[X]/(h ∘ f)`.

The proof reduces the assertion, by base change along the injective map
`A → AlgebraicClosure (FractionRing A)`, to the case of an algebraically closed field, where both
sides are computed as products of values of `g` over the roots of the relevant polynomials, and the
two multisets of roots are identified via `h ∘ f = ∏_{β : h(β) = 0} (f - C β)`.

## Main results

* `NK.LocalReciprocityLubinTate.Unramified.normOp_map` — base change for `normOp`;
* `NK.LocalReciprocityLubinTate.Unramified.resultant_normOp_algClosed` — the identity over an
  algebraically closed field;
* `NK.LocalReciprocityLubinTate.Unramified.resultant_normOp` — the general identity.
-/

namespace NK.LocalReciprocityLubinTate.Unramified

open Polynomial

universe u v

/-- **Base change for the norm operator.**  If `φ : A →+* B` is an injective ring map between
domains and `f` is monic of positive degree, then `normOp` commutes with the induced map on
polynomials. -/
theorem normOp_map {A : Type u} [CommRing A] [IsDomain A] {B : Type v} [CommRing B] [IsDomain B]
    (φ : A →+* B) (hφ : Function.Injective φ) (f g : Polynomial A) (hf : f.Monic)
    (hd : 0 < f.natDegree) :
    (normOp f g).map φ = normOp (f.map φ) (g.map φ) := by
  rw [normOp_def, normOp_def]
  have key := Polynomial.resultant_map_map
      (Polynomial.map Polynomial.C f - Polynomial.C (Polynomial.X : Polynomial A))
      (Polynomial.map Polynomial.C g)
      (Polynomial.map Polynomial.C f - Polynomial.C (Polynomial.X : Polynomial A)).natDegree
      (Polynomial.map Polynomial.C g).natDegree
      (Polynomial.mapRingHom φ)
  rw [← Polynomial.coe_mapRingHom]
  rw [← key]
  have hC : ∀ p : Polynomial A, (Polynomial.map Polynomial.C p).map (Polynomial.mapRingHom φ)
      = Polynomial.map Polynomial.C (p.map φ) := by
    intro p
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext a
    simp
  have hX : (Polynomial.C (Polynomial.X : Polynomial A)).map (Polynomial.mapRingHom φ)
      = Polynomial.C (Polynomial.X : Polynomial B) := by
    simp
  have hp : (Polynomial.map Polynomial.C f - Polynomial.C (Polynomial.X : Polynomial A)).map
        (Polynomial.mapRingHom φ)
      = Polynomial.map Polynomial.C (f.map φ) - Polynomial.C (Polynomial.X : Polynomial B) := by
    rw [Polynomial.map_sub, hC f, hX]
  have hq : (Polynomial.map Polynomial.C g).map (Polynomial.mapRingHom φ)
      = Polynomial.map Polynomial.C (g.map φ) := hC g
  have hdf : (Polynomial.map Polynomial.C f - Polynomial.C (Polynomial.X : Polynomial A)).natDegree
      = (Polynomial.map Polynomial.C (f.map φ) - Polynomial.C (Polynomial.X : Polynomial B)).natDegree := by
    rw [natDegree_map_C_sub_C_X f hf hd,
        natDegree_map_C_sub_C_X (f.map φ) (hf.map φ)
          (by rw [Polynomial.Monic.natDegree_map hf φ]; exact hd)]
    exact (Polynomial.Monic.natDegree_map hf φ).symm
  have hdg : (Polynomial.map Polynomial.C g).natDegree
      = (Polynomial.map Polynomial.C (g.map φ)).natDegree := by
    rw [natDegree_map_C g, natDegree_map_C (g.map φ), Polynomial.natDegree_map_eq_of_injective hφ g]
  rw [hp, hq, hdf, hdg]
  rfl

/-- **The resultant identity over an algebraically closed field.**  For `L` algebraically closed,
`f` monic of positive degree and `h` monic, `Res_Y(h, normOp f g) = Res_X(h ∘ f, g)`. -/
theorem resultant_normOp_algClosed {L : Type v} [Field L] [IsAlgClosed L]
    (f h g : Polynomial L) (hf : f.Monic) (hd : 0 < f.natDegree) (hh : h.Monic) :
    h.resultant (normOp f g) = (h.comp f).resultant g := by
  have hsub : ∀ β : L, (f - C β).Monic := fun β =>
    hf.sub_of_left (lt_of_le_of_lt degree_C_le (by rw [degree_eq_natDegree hf.ne_zero]; exact_mod_cast hd))
  have hmon : (h.comp f).Monic := hh.comp hf hd.ne'
  have hne : ∀ β : L, f - C β ≠ 0 := by
    intro β hβ
    have h := Polynomial.natDegree_sub_C (p := f) (a := β)
    rw [hβ, Polynomial.natDegree_zero] at h
    omega
  rw [Polynomial.resultant_eq_prod_eval h (normOp f g) (normOp f g).natDegree le_rfl
        (IsAlgClosed.splits h), hh.leadingCoeff, one_pow, one_mul]
  rw [Polynomial.resultant_eq_prod_eval (h.comp f) g g.natDegree le_rfl (IsAlgClosed.splits _),
      hmon.leadingCoeff, one_pow, one_mul]
  have hNfun : (normOp f g).eval = fun β => ((f - C β).roots.map g.eval).prod := by
    funext β
    rw [show (normOp f g).eval β = (f - C β).resultant g from normOp_eval f g hf hd β]
    rw [Polynomial.resultant_eq_prod_eval (f - C β) g g.natDegree le_rfl (IsAlgClosed.splits _)]
    rw [(hsub β).leadingCoeff, one_pow, one_mul]
  simp only [hNfun]
  rw [← Multiset.prod_bind (h.roots) (fun β => (f - C β).roots.map g.eval)]
  rw [← Multiset.map_bind (h.roots) (fun β => (f - C β).roots) (Polynomial.eval · g)]
  have h1 : h = (h.roots.map fun a => X - C a).prod :=
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hh
      (IsAlgClosed.splits h).natDegree_eq_card_roots.symm).symm
  have h2 : h.comp f = (h.roots.map fun β => f - C β).prod := by
    conv_lhs => rw [h1]
    rw [Polynomial.multiset_prod_comp, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro β _
    simp
  have hside : 0 ∉ h.roots.map (fun β => f - C β) := by
    rw [Multiset.mem_map]
    rintro ⟨β, -, hβ⟩
    exact hne β hβ
  have h3 : h.roots.bind (fun β => (f - C β).roots) = (h.comp f).roots := by
    rw [← Multiset.bind_map (h.roots) (Polynomial.roots) (fun β => f - C β),
        ← Polynomial.roots_multiset_prod (h.roots.map (fun β => f - C β)) hside,
        ← h2]
  rw [h3]

/-- **The resultant identity for the norm operator.**  For a commutative ring `A`, polynomials
`f, h, g ∈ A[X]` with `f, h` monic and `0 < deg f`,

`Res_Y(h, normOp f g) = Res_X(h ∘ f, g)`. -/
theorem resultant_normOp {A : Type u} [CommRing A] [IsDomain A] (f h g : Polynomial A)
    (hf : f.Monic) (hd : 0 < f.natDegree) (hh : h.Monic) :
    h.resultant (NK.LocalReciprocityLubinTate.Unramified.normOp f g)
      = (h.comp f).resultant g := by
  let L := AlgebraicClosure (FractionRing A)
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) L]
    exact (FaithfulSMul.algebraMap_injective (FractionRing A) L).comp
      (IsFractionRing.injective A (FractionRing A))
  apply hinj
  have h1 := Polynomial.resultant_map_map h (normOp f g) h.natDegree (normOp f g).natDegree
    (algebraMap A L)
  have h2 := Polynomial.resultant_map_map (h.comp f) g (h.comp f).natDegree g.natDegree
    (algebraMap A L)
  rw [← h1, ← h2]
  have hNmap := normOp_map (algebraMap A L) hinj f g hf hd
  have e1 : h.natDegree = (h.map (algebraMap A L)).natDegree :=
    (Polynomial.natDegree_map_eq_of_injective hinj h).symm
  have e2 : (normOp f g).natDegree
      = (normOp (f.map (algebraMap A L)) (g.map (algebraMap A L))).natDegree := by
    rw [← hNmap, Polynomial.natDegree_map_eq_of_injective hinj]
  have e3 : (h.comp f).natDegree
      = ((h.map (algebraMap A L)).comp (f.map (algebraMap A L))).natDegree := by
    rw [← Polynomial.map_comp (algebraMap A L) h f, Polynomial.natDegree_map_eq_of_injective hinj]
  have e4 : g.natDegree = (g.map (algebraMap A L)).natDegree :=
    (Polynomial.natDegree_map_eq_of_injective hinj g).symm
  rw [hNmap, Polynomial.map_comp, e1, e2, e3, e4]
  exact resultant_normOp_algClosed (f.map (algebraMap A L)) (h.map (algebraMap A L))
    (g.map (algebraMap A L)) (hf.map _)
    (by rw [Polynomial.Monic.natDegree_map hf]; exact hd) (hh.map _)

end NK.LocalReciprocityLubinTate.Unramified
