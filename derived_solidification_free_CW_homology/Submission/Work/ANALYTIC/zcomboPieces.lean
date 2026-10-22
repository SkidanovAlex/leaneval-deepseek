import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.zmap_ext_of_closed_cover
import Submission.Work.ANALYTIC.pointsDetectSetup

/-!
# Setup for `Work.ANALYTIC.zfree_zmap_combo_locally_zero`

A finite family of maps `φ j : V ⟶ T` (`j : Fin m`) out of a light profinite set and a
finite family of coefficients `c j` give the morphism
`∑ j, c j • zmap (φ j) : ℤ[V] ⟶ ℤ[T]`, written `Work.ANALYTIC.zmapCombo φ c`.
The point of this file is the "finiteness" input needed to show that such a combination which
vanishes at every *point* of `V` is zero on a *finite cover* of `V`:

* `fiber_sum_eq_zero` — the key grouping fact.  If `∑ j, c j • [t j] = 0` in `ℤ[T]` (a relation
  between point classes, expressed on the level of morphisms `ℤ[∗] ⟶ ℤ[T]`) and the points
  `t j` are *not* assumed distinct, then the coefficients summed over each fibre
  `{j | t j = t i}` still vanish.  This is where `hind` (linear independence of the point classes
  of an injective tuple of points) enters.

* the *pieces* `pieceSet V T φ f` — for a "pattern" function `f : Fin m → Fin m` these are the
  closed subsets of `V` on which `φ i = φ j` whenever `f i = f j`; the induced light profinite
  set is `piece V T φ f` with inclusion `pieceIncl V T φ f : piece V T φ f ⟶ V`.

The cover used for the main theorem consists of the pieces of the *idempotent* pattern functions
`f` whose class coefficient sums vanish (`Work.ANALYTIC.piece_family_covers`), and the combination
restricts to `0` on each such piece (`Work.ANALYTIC.zmapCombo_restrict_piece_zero`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite Classical

noncomputable section

namespace Work.ANALYTIC

variable (V T : LightProfinite.{0}) (m : ℕ) (φ : Fin m → (V ⟶ T))

/-! ### The grouping lemma for point classes -/

/-- **Fibre sums of a relation between point classes vanish.**

`hind` is the linear independence of the point classes of an injective tuple of points of `T`
(`Work.ANALYTIC.pointClassM T t : ℤ[∗] ⟶ ℤ[T]`, the class of the point `t`).  Given a relation
`∑ j, c j • [t j] = 0` for an arbitrary (not necessarily injective) tuple `t`, the sum of the
coefficients over each fibre `{j | t j = t i}` is zero: restricting to one point of each fibre
leaves a relation between the point classes of pairwise *distinct* points, to which `hind`
applies. -/
theorem fiber_sum_eq_zero
    (hind : ∀ (m : ℕ) (t : Fin m → ↥T), Function.Injective t → ∀ c : Fin m → ℤ,
      (∑ j, c j • (pointClassM T (t j))) = 0 → ∀ j, c j = 0)
    {m : ℕ} (t : Fin m → ↥T) (c : Fin m → ℤ)
    (h : ∑ j, c j • (pointClassM T (t j)) = 0) :
    ∀ i : Fin m, ∑ k ∈ Finset.univ.filter (fun k => t k = t i), c k = 0 := by
  intro i
  set S : Finset ↥T := Finset.univ.image t with hS
  have hmemS : ∀ j : Fin m, t j ∈ S := fun j => by simp [hS]
  let e : Fin (Fintype.card {x : ↥T // x ∈ S}) ≃ {x : ↥T // x ∈ S} := (Fintype.equivFin _).symm
  have hinj : Function.Injective (fun k : Fin (Fintype.card {x : ↥T // x ∈ S}) => (e k).1) := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  have hsum : (∑ k : Fin (Fintype.card {x : ↥T // x ∈ S}),
      (∑ j ∈ Finset.univ.filter (fun j => t j = (e k).1), c j) •
        pointClassM T ((e k).1)) = 0 := by
    rw [Equiv.sum_comp (M := (Work.ATOM.zfree Work.ATOM.pt ⟶ Work.ATOM.zfree T)) e
      (fun x : {x : ↥T // x ∈ S} =>
        (∑ j ∈ Finset.univ.filter (fun j => t j = x.1), c j) •
          pointClassM T (x.1))]
    rw [← Finset.sum_subtype (p := fun x => x ∈ S) S (fun x => Iff.rfl)
      (fun x : ↥T => (∑ j ∈ Finset.univ.filter (fun j => t j = x), c j) •
        pointClassM T x)]
    calc ∑ a ∈ S, (∑ j ∈ Finset.univ.filter (fun j => t j = a), c j) • pointClassM T a
        = ∑ a ∈ S, ∑ j ∈ Finset.univ.filter (fun j => t j = a), c j •
            pointClassM T (t j) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [(Finset.mem_filter.mp hj).2]
      _ = ∑ j, c j • pointClassM T (t j) :=
          Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := t)
            (fun j _ => hmemS j) (fun j => c j • pointClassM T (t j))
      _ = 0 := h
  have hzero := hind _ (fun k => (e k).1) hinj
    (fun k => ∑ j ∈ Finset.univ.filter (fun j => t j = (e k).1), c j) hsum
  have hkey : (∑ j ∈ Finset.univ.filter (fun j => t j = (e (e.symm ⟨t i, hmemS i⟩)).1), c j)
      = ∑ k ∈ Finset.univ.filter (fun k => t k = t i), c k := by
    simp
  rw [← hkey, hzero]

/-! ### The pieces of the cover -/

/-- For a "pattern" function `f : Fin m → Fin m`, the closed subset of `V` on which the maps
`φ i` and `φ j` agree whenever `f i = f j`. -/
def pieceSet (f : Fin m → Fin m) : Set ↥V := {v | ∀ i j : Fin m, f i = f j → φ i v = φ j v}

/-- `pieceSet φ f` is closed: an intersection over the pairs `(i, j)` of the equalisers of
`φ i` and `φ j` (for the pairs with `f i = f j`) and of the whole space (otherwise). -/
theorem isClosed_pieceSet (f : Fin m → Fin m) : IsClosed (pieceSet V T m φ f) := by
  have hset : pieceSet V T m φ f
      = ⋂ i : Fin m, ⋂ j : Fin m, {v : ↥V | f i = f j → φ i v = φ j v} := by
    ext v
    simp only [pieceSet, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : f i = f j
  · have : {v : ↥V | f i = f j → φ i v = φ j v} = {v : ↥V | φ i v = φ j v} := by
      ext v; simp [hij]
    rw [this]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  · have : {v : ↥V | f i = f j → φ i v = φ j v} = Set.univ := by
      ext v; simp [hij]
    rw [this]; exact isClosed_univ

instance instCompactSpacePieceSet (f : Fin m → Fin m) : CompactSpace ↥(pieceSet V T m φ f) :=
  isCompact_iff_compactSpace.mp (isClosed_pieceSet V T m φ f).isCompact

/-- The piece of `V` cut out by the pattern `f`, as a light profinite set. -/
def piece (f : Fin m → Fin m) : LightProfinite.{0} := LightProfinite.of ↥(pieceSet V T m φ f)

/-- The inclusion of the piece `piece V T φ f` into `V`. -/
def pieceIncl (f : Fin m → Fin m) : piece V T m φ f ⟶ V :=
  ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp] lemma pieceIncl_apply (f : Fin m → Fin m) (x : ↥(piece V T m φ f)) :
    pieceIncl V T m φ f x = x.1 := rfl

end Work.ANALYTIC

end
