/-
# The letters of a reduced path in the Bass--Serre star tree avoid the base subgroup

Let `φ : (i : ι) → H →* G i` be a family of group homomorphisms, `P = Psh φ` the pushout,
`baseSub φ ≤ P` the image of `H` and `Vtx φ` the "star" graph of
`Submission.Work.ORLocInd.FKSKernel.PushoutStarTree` on which `P` acts.
For a path `p` in this graph starting at the centre `ctr φ γ`, the list `clets φ γ p`
(`PushoutStarTreeTree`) records the letters of `p`: at every step from a leaf back to a
centre it records the ratio `(repC c)⁻¹ * repC c'` of the representatives of the two
successive centres `c`, `c'`, tagged by the type of the step.

The main result of this file is that **if `p` is reduced, then every letter of `p` lies
outside the base subgroup `baseSub φ`**.  Since `(repC c)⁻¹ * repC c' ∈ baseSub φ` exactly
when `c = c'`, this says precisely that a reduced path never crosses the same centre coset
twice in a row, i.e. it never immediately backtracks, which is the compatibility of `clets`
with the tree structure of `Vtx φ`.

The proof is by induction on the path.  In the step `p = q.cons e` with `q` of odd length
(so that `q` ends at a leaf and `e` leaves that leaf) the only new letter is
`(repC (cstateC φ γ q))⁻¹ * repC (Arrow.lbl e)`, and the content is that a reduced path
which enters a leaf from a centre cannot leave it towards that same centre: doing so would
make the last two arrows of `p` mutually inverse, contradicting reducedness.  This is the
technical lemma `not_isReduced_cons_cons_of_lbl_eq` below; the bookkeeping of the endpoints
is handled by the general quiver lemmas `cons_cast_mid`, `Arrow.cast_fst` and
`not_isReduced_cons_cons_reverse`.
-/
import Mathlib
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTree
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTreeTree

namespace Work.ORLocInd.FKSKernel

open Quiver

universe u

variable {ι : Type u} {H : Type u} {G : ι → Type u} [Group H] [∀ i, Group (G i)]
variable {φ : ∀ i, H →* G i} {γ : Psh φ ⧸ baseSub φ}

/-! ## General quiver lemmas about transporting endpoints -/

/-- Casting along an equality of the *middle* vertex of a one-arrow extension of a path. -/
theorem cons_cast_mid {V : Type*} [Quiver V] {a v w v' : V} (p : Quiver.Path a v) (e : v ⟶ w)
    (h : v = v') : p.cons e = (p.cast rfl h).cons (e.cast h rfl) := by
  cases h
  simp

/-- The underlying data `ι × Psh φ` of an arrow of the star tree is unchanged by transporting
the arrow along equalities of its endpoints. -/
theorem Arrow.cast_fst {x x' y y' : Vtx φ} (hu : x = x') (hv : y = y') (e : x ⟶ y) :
    (e.cast hu hv).1 = e.1 := by
  cases hu
  cases hv
  simp

/-- Reversal commutes with the transport of an arrow along equalities of its endpoints. -/
theorem reverse_hom_cast {V : Type*} [Quiver V] [Quiver.HasReverse V] {u v u' v' : V}
    (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    Quiver.reverse (e.cast hu hv) = (Quiver.reverse e).cast hv hu := by
  cases hu; cases hv; simp

/-- In a quiver with a reversal, a path whose last two arrows are mutually inverse is not
reduced. -/
theorem not_isReduced_cons_cons_reverse {V : Type*} [Quiver V] [Quiver.HasReverse V] {a x y : V}
    (r : Quiver.Path a y) (e' : y ⟶ x) (e : x ⟶ y) (he : e = Quiver.reverse e') :
    ¬ ((r.cons e').cons e).IsReduced := by
  intro h
  refine h r ?_
  rw [he]
  simpa using (Quiver.Path.DeleteBacktrack.intro r e' Quiver.Path.nil)

/-! ## The star tree: a reduced path cannot go back where it came from -/

/-- If `e'` is an arrow from the centre `ctr φ c` into a leaf and `e` leaves that leaf towards
the same centre, then the two arrows are mutually inverse; hence such a step cannot occur in a
reduced path. -/
theorem not_isReduced_cons_cons_of_lbl_eq {x' x y : Vtx φ} (r : Quiver.Path (ctr φ γ) x')
    (e' : x' ⟶ x) (e : x ⟶ y) (c : Psh φ ⧸ baseSub φ) (hx' : x' = ctr φ c)
    (he : Arrow.lbl e = c) : ¬ ((r.cons e').cons e).IsReduced := by
  -- `e'` goes from the centre `c` to the leaf `lf φ e'.idx c`
  have he'info : Arrow.lbl e' = c ∧ x = lf φ (Arrow.idx e') (Arrow.lbl e') := by
    rcases Arrow.endpoints e' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨ctr_inj (h1.symm.trans hx'), h2⟩
    · exact absurd (hx'.symm.trans h1) (ctr_ne_lf φ c (Arrow.lbl e') (Arrow.idx e'))
  obtain ⟨he'lbl, hxlf'⟩ := he'info
  -- since `x` is a leaf, `e` goes from that leaf to the centre `ctr φ e.lbl`
  have heinfo : x = lf φ (Arrow.idx e) (Arrow.lbl e) ∧ y = ctr φ (Arrow.lbl e) := by
    rcases Arrow.endpoints e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h1.symm.trans hxlf')
        (ctr_ne_lf φ (Arrow.lbl e) (Arrow.lbl e') (Arrow.idx e'))
    · exact ⟨h1, h2⟩
  obtain ⟨hxlf, hylbl⟩ := heinfo
  -- the two arrows carry the same data `(idx, lbl)`
  have hidx : Arrow.idx e = Arrow.idx e' :=
    (leaf_eq_components (hxlf.symm.trans hxlf')).1
  have hdata : e.1 = e'.1 := Prod.ext hidx (he.trans he'lbl.symm)
  -- and `e` ends at `x'`, so that `e` is literally the reverse of the transported `e'`
  have hy : y = x' := by
    rw [hylbl, he]
    exact hx'.symm
  have hrev : e = Quiver.reverse (e'.cast hy.symm rfl) := by
    rw [reverse_hom_cast]
    exact Subtype.ext (by rw [Arrow.cast_fst, reverse_val, hdata])
  intro hred
  have hcons : (r.cons e').cons e = ((r.cast rfl hy.symm).cons (e'.cast hy.symm rfl)).cons e := by
    rw [cons_cast_mid r e' hy.symm]
  rw [hcons] at hred
  exact not_isReduced_cons_cons_reverse (r.cast rfl hy.symm) (e'.cast hy.symm rfl) e hrev hred

/-- A path of even length starting at a centre ends at a centre: the endpoint is the centre of
its state `cstateC`. -/
theorem eq_ctr_cstateC_of_length_even (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ)
    {x : Vtx φ} (p : Quiver.Path (ctr φ γ) x) (h : p.length % 2 = 0) :
    x = ctr φ (cstateC φ γ p) := by
  rcases cstateC_spec φ γ x p with ⟨c, hx, hst⟩ | ⟨i, hx⟩
  · rw [← hst] at hx; exact hx
  · exact absurd ((length_even_iff_ctr φ γ x p).mpr h)
      (fun ⟨c, hc⟩ => ctr_ne_lf φ c (cstateC φ γ p) i (hc.symm.trans hx))

/-- **The key step.**  If `p = q.cons e` is reduced and `q` has odd length (so that `q` ends at
a leaf), then the arrow `e` leaves that leaf towards a centre different from the centre from
which the leaf was entered, i.e. `Arrow.lbl e ≠ cstateC φ γ q`. -/
theorem lbl_ne_cstateC_of_isReduced {x y : Vtx φ}
    (q : Quiver.Path (ctr φ γ) x) (e : x ⟶ y)
    (h : (q.cons e).IsReduced) (hodd : q.length % 2 = 1) :
    Arrow.lbl e ≠ cstateC φ γ q := by
  intro he
  cases q with
  | nil => simp at hodd
  | cons r e' =>
    rw [cstateC_cons, if_neg] at he
    · have hre : r.length % 2 = 0 := by
        simp only [Quiver.Path.length_cons] at hodd
        omega
      exact not_isReduced_cons_cons_of_lbl_eq r e' e (cstateC φ γ r)
        (eq_ctr_cstateC_of_length_even φ γ r hre) he h
    · simp only [Quiver.Path.length_cons] at hodd
      omega

/-! ## Comparing cosets through the chosen representatives -/

/-- `(repC φ c)⁻¹ * repC φ c'` lies in the base subgroup exactly when the two cosets agree. -/
theorem inv_mul_repC_mem_iff (c d : Psh φ ⧸ baseSub φ) :
    (repC φ c)⁻¹ * repC φ d ∈ baseSub φ ↔ c = d := by
  rw [← QuotientGroup.eq]
  simp only [QuotientGroup.mk, repC_mk]

/-! ## The main theorem -/

/-- Every letter of a reduced path starting at a centre of the star tree lies outside the base
subgroup. -/
theorem clets_notMem_baseSub_of_isReduced {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) {y : Vtx φ}
    (p : Quiver.Path (ctr φ γ) y) (hp : p.IsReduced) :
    ∀ x ∈ clets φ γ p, x.2 ∉ baseSub φ := by
  revert hp
  induction p with
  | nil =>
    intro hp x hx
    simp only [clets_nil] at hx
    simp at hx
  | cons q e ih =>
    intro hp x hx
    rw [clets_cons] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih (Quiver.Path.IsReduced.of_comp (p := q) (q := e.toPath) hp) x hx
    · by_cases hodd : q.length % 2 = 1
      · rw [if_pos hodd, List.mem_singleton] at hx
        subst hx
        intro hmem
        exact lbl_ne_cstateC_of_isReduced q e hp hodd
          ((inv_mul_repC_mem_iff _ _).mp hmem).symm
      · rw [if_neg hodd] at hx
        simp at hx

end Work.ORLocInd.FKSKernel
