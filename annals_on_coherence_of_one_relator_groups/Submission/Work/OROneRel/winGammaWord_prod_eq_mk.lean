import Mathlib
import Submission.Work.OROneRel.hnnSplitPin

/-!
# The product of the signed coedge words is the `FreeGroup.mk` of the filterMap

`winGammaWord Wt c lo hi p` is the `β`-word of the *positive* traversal `(p, true)` of the edge
`p` of the cover: it is the generator of `β` when `p` is a non-tree edge of the window, and `1`
otherwise (`hnnSplitPin.winGammaWord`).  The general statement proved here is that for **any** list
`L` of decorated letters, the product of the signed coedge words

`fun p => if p.2 then winGammaWord p.1 else (winGammaWord p.1)⁻¹`

is exactly the free-group word spelled by `L.filterMap (winRootStep ...)`.  Since `winRootStep`
keeps a letter precisely when its edge lies in the window and has non-trivial loop class, and
records the sign of the traversal, this says: *the product of the signed coedge words of `L` is the
word obtained from `L` by deleting the letters outside `winBeta`*.

The proof is the general list identity `filterMap_map_prod` (`(l.filterMap f).map g` is the product
of `(f d).elim 1 g` over `l`) together with the two facts

* `FreeGroup.mk l = (l.map (fun q => if q.2 then of q.1 else (of q.1)⁻¹)).prod`, which is
  `FreeGroup.lift_mk` for the identity map (`mk_eq_prod_signed`), and
* the pointwise comparison `winRootStep_signed_apply`, which says that the letter `d` contributes
  `winGammaWord d.1` (resp. its inverse) according to the sign `d.2`, and `1` when `winRootStep`
  deletes it.

Everything reduces to the sign convention: `winRootStep (p, b)` keeps `p` with *the sign* `b`, so
the coedge word of a traversal in the negative direction is the inverse of the coedge word of the
edge, while `winGammaWord` only ever sees the positive traversal `(p, true)`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## `FreeGroup.mk` as a product of signed letters -/

/-- **`FreeGroup.mk` of a signed list is the product of its signed letters.** -/
theorem mk_eq_prod_signed {β : Type*} (l : List (β × Bool)) :
    FreeGroup.mk l
      = (l.map (fun q => if q.2 then FreeGroup.of q.1 else (FreeGroup.of q.1)⁻¹)).prod := by
  have h1 : (FreeGroup.lift (FreeGroup.of : β → FreeGroup β)) = MonoidHom.id (FreeGroup β) :=
    (FreeGroup.lift (α := β) (β := FreeGroup β)).right_inv (MonoidHom.id (FreeGroup β))
  have h2 := FreeGroup.lift_mk (f := (FreeGroup.of : β → FreeGroup β)) (L := l)
  rw [h1] at h2
  simp only [MonoidHom.id_apply] at h2
  rw [h2]
  simp only [cond_eq_ite]

/-! ## Computing `winRootStep` -/

/-- `winRootStep` deletes a decorated letter whose edge does not lie in the window or has trivial
loop class (the complement of the defining condition). -/
theorem winRootStep_eq_none {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    (p : (α × ℤ) × Bool) (h : ¬ (p.1 ∈ winE c lo hi ∧ coverClassAt Wt c p.1 ≠ 1)) :
    winRootStep Wt c lo hi p = none := by
  classical
  unfold winRootStep
  exact dif_neg h

/-- **The letter contributed by a decorated letter.**  Under the step function `winRootStep`, the
decorated letter `p` contributes the coedge word of its edge `p.1` -- or its inverse, according to
the sign `p.2` -- and `1` when `winRootStep` deletes it. -/
theorem winRootStep_signed_apply {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    (p : (α × ℤ) × Bool) :
    (winRootStep Wt c lo hi p).elim (1 : FreeGroup (winBeta Wt c lo hi))
        (fun q => if q.2 then FreeGroup.of q.1 else (FreeGroup.of q.1)⁻¹)
      = if p.2 then winGammaWord Wt c lo hi p.1
        else (winGammaWord Wt c lo hi p.1)⁻¹ := by
  classical
  by_cases h : p.1 ∈ winE c lo hi ∧ coverClassAt Wt c p.1 ≠ 1
  · have h1 : winRootStep Wt c lo hi p = some (⟨p.1, h.1, h.2⟩, p.2) :=
      winRootStep_of Wt c lo hi p h.1 h.2
    have h2 : winRootStep Wt c lo hi (p.1, true) = some (⟨p.1, h.1, h.2⟩, true) :=
      winRootStep_of Wt c lo hi (p.1, true) h.1 h.2
    have hg : winGammaWord Wt c lo hi p.1
        = FreeGroup.of (⟨p.1, h.1, h.2⟩ : winBeta Wt c lo hi) := by
      rw [winGammaWord, h2]
      rfl
    rw [h1, hg]
    cases p.2 <;> rfl
  · have h1 : winRootStep Wt c lo hi p = none := winRootStep_eq_none p h
    have h2 : winRootStep Wt c lo hi (p.1, true) = none := winRootStep_eq_none (p.1, true) h
    have hg : winGammaWord Wt c lo hi p.1 = (1 : FreeGroup (winBeta Wt c lo hi)) := by
      rw [winGammaWord, h2]
      rfl
    rw [h1, hg]
    cases p.2 <;> rfl

/-! ## The product identity -/

theorem winGammaWord_prod_eq_mk {α : Type u} {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    (L : List ((α × ℤ) × Bool)) :
    (L.map (fun p => if p.2 then Work.OROneRel.winGammaWord Wt c lo hi p.1
      else (Work.OROneRel.winGammaWord Wt c lo hi p.1)⁻¹)).prod
      = FreeGroup.mk (L.filterMap (Work.OROneRel.winRootStep Wt c lo hi)) := by
  classical
  have hmap : L.map (fun d => (winRootStep Wt c lo hi d).elim (1 : FreeGroup (winBeta Wt c lo hi))
        (fun q => if q.2 then FreeGroup.of q.1 else (FreeGroup.of q.1)⁻¹))
      = L.map (fun p => if p.2 then winGammaWord Wt c lo hi p.1
          else (winGammaWord Wt c lo hi p.1)⁻¹) :=
    List.map_congr_left (fun p _ => winRootStep_signed_apply p)
  rw [mk_eq_prod_signed, filterMap_map_prod L (winRootStep Wt c lo hi)
    (fun q : winBeta Wt c lo hi × Bool =>
      if q.2 then FreeGroup.of q.1 else (FreeGroup.of q.1)⁻¹), hmap]

end Work.OROneRel
