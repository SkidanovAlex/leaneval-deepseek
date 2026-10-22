import Mathlib
import Submission.Work.ANALYTIC.zcomboPieces
import Submission.Work.ANALYTIC.pointsDetectSetup

/-!
# `zmapCombo_restrict_piece_zero`

Let `φ : Fin m → (V ⟶ T)` be a finite family of maps of light profinite sets and `c : Fin m → ℤ`
a finite family of coefficients.  For an idempotent pattern function `f : Fin m → Fin m`
(`f ∘ f = f`) consider the piece

`pieceSet φ f = {v : ↥V | ∀ i j, f i = f j → φ i v = φ j v}`

and its inclusion `pieceIncl : piece φ f ⟶ V`.

The main theorem of this file says that if the coefficients of `c` sum to zero over every
`f`-fibre, i.e. `∑ k ∈ {k | f k = f i}, c k = 0` for all `i`, then the combination
`∑ j, c j • ℤ[pieceIncl ≫ φ j]` vanishes on the piece.

The mathematical content is one line: on the piece, `φ j` and `φ (f j)` agree (apply the
definition of `pieceSet` to the pair `(f j, j)`, using `f (f j) = f j`); hence
`∑ j, c j • ℤ[pieceIncl ≫ φ j] = ∑ j, c j • ℤ[pieceIncl ≫ φ (f j)]`, and grouping the latter sum
by the value of `f` (each group sits in a fibre of `f`, where the coefficient sum vanishes)
gives `0`.

The combinatorial grouping is isolated as the general lemma
`Work.ANALYTIC.sum_smul_eq_zero_of_idempotent_fiber` (stated for an arbitrary abelian group, and
independent of the condensed-mathematics context), and the coincidence of `φ j` and `φ (f j)`
on the piece is `Work.ANALYTIC.pieceIncl_comp_phi_f`.

This is the "zero on each piece" input for the local-to-global principle
`Work.ANALYTIC.piece_family_covers`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite Classical

noncomputable section

namespace Work.ANALYTIC

/-! ### The combinatorial grouping lemma -/

/-- **A combination of `f`-invariant data grouped by the fibres of an idempotent vanishes when
the fibre sums of the coefficients do.**

Let `f : Fin m → Fin m` be idempotent (`f (f i) = f i`), `c : Fin m → ℤ` with vanishing fibre
sums `∑ k ∈ {k | f k = f i}, c k = 0`, and `g : Fin m → M` a family in an abelian group whose
values are constant along `f` (`g (f i) = g i`).  Then `∑ i, c i • g i = 0`.

Indeed one may replace `g i` by `g (f i)`, and then group the sum by the value of `f`: on the
fibre `{k | f k = y}` over a point `y` of the image of `f` (so that `f y = y`), the factor
`g (f k) = g y` is constant, so the corresponding sub-sum is
`(∑ k ∈ {k | f k = f y}, c k) • g y = 0`. -/
lemma sum_smul_eq_zero_of_idempotent_fiber {M : Type*} [AddCommGroup M] {m : ℕ}
    (f : Fin m → Fin m) (hf : ∀ i, f (f i) = f i) (c : Fin m → ℤ) (g : Fin m → M)
    (hg : ∀ i, g (f i) = g i)
    (hc : ∀ i, ∑ k ∈ Finset.univ.filter (fun k => f k = f i), c k = 0) :
    ∑ i, c i • g i = 0 := by
  set S : Finset (Fin m) := Finset.univ.image f with hS
  have hstep : ∑ i, c i • g i = ∑ i, c i • g (f i) :=
    Finset.sum_congr rfl (fun i _ => by rw [hg i])
  rw [hstep]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := f)
    (fun i _ => by simp [hS]) (fun i => c i • g (f i))]
  refine Finset.sum_eq_zero (fun y hy => ?_)
  obtain ⟨y₀, -, hy₀⟩ := Finset.mem_image.mp (by simpa [hS] using hy : y ∈ Finset.univ.image f)
  have hfy : f y = y := by rw [← hy₀, hf y₀]
  have h₁ : ∑ x ∈ Finset.univ.filter (fun x => f x = y), c x • g (f x)
      = ∑ x ∈ Finset.univ.filter (fun x => f x = y), c x • g y := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [(Finset.mem_filter.mp hx).2]
  rw [h₁, ← Finset.sum_smul]
  rw [show Finset.univ.filter (fun x => f x = y) = Finset.univ.filter (fun x => f x = f y)
      from by rw [hfy], hc y, zero_smul]

/-! ### The maps `φ j` and `φ (f j)` agree on the piece -/

/-- On the piece `piece V T m φ f`, the maps `φ j` and `φ (f j)` coincide: the defining property
of the piece applied to the pair `(f j, j)` uses exactly the idempotence `f (f j) = f j`. -/
lemma pieceIncl_comp_phi_f (V T : LightProfinite.{0}) (m : ℕ) (φ : Fin m → (V ⟶ T))
    (f : Fin m → Fin m) (hf : ∀ i, f (f i) = f i) (j : Fin m) :
    (pieceIncl V T m φ f) ≫ φ (f j) = (pieceIncl V T m φ f) ≫ φ j := by
  ext x
  simp only [ConcreteCategory.comp_apply, pieceIncl_apply]
  exact x.2 (f j) j (hf j)

/-! ### The main theorem -/

/-- **The combination `∑ j, c j • ℤ[pieceIncl ≫ φ j]` vanishes on each piece of the pattern `f`**
(whose fibre coefficient sums vanish). -/
theorem zmapCombo_restrict_piece_zero (V T : LightProfinite.{0}) (m : ℕ)
    (φ : Fin m → (V ⟶ T)) (c : Fin m → ℤ) (f : Fin m → Fin m)
    (hf : ∀ i, f (f i) = f i)
    (hc : ∀ i, ∑ k ∈ Finset.univ.filter (fun k => f k = f i), c k = 0) :
    Work.ANALYTIC.zmapCombo (fun j => CategoryTheory.CategoryStruct.comp (Work.ANALYTIC.pieceIncl V T m φ f) (φ j)) c = 0 := by
  show (∑ j : Fin m, c j • Work.ATOM.zmap ((Work.ANALYTIC.pieceIncl V T m φ f) ≫ φ j)) = 0
  exact sum_smul_eq_zero_of_idempotent_fiber f hf c
    (fun j => Work.ATOM.zmap ((Work.ANALYTIC.pieceIncl V T m φ f) ≫ φ j))
    (fun i => congrArg Work.ATOM.zmap (pieceIncl_comp_phi_f V T m φ f hf i)) hc

end Work.ANALYTIC
