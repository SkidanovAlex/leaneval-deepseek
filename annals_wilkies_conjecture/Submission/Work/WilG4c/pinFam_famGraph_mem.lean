/-
  WilG4c — `pinFam_famGraph_mem`: the graph of the *pinned* family is the graph of `f` read
  through a relabelling of the ambient coordinates that changes no dimension — hence at *zero*
  cost in the `Ω`-format and `Ω`-degree.

  `Work.WilkG4c.pinFam p n f` is `f` with the distinguished cube coordinate `x` moved into the
  parameter block: `pinFam p n f (l, x) y = f l (x, y)`.  Its graph lives in `ℝ^{(p+1)+n+1}` in the
  layout `(l, x, y, s)`; the graph of `f` lives in `ℝ^{p+(n+1)+1}` in the *same* layout, the block
  boundaries being `p | 1 | n | 1` instead of `p | (n+1) | 1`.  The two index types have the same
  number of elements (`p + (n+1) + 1 = (p+1) + n + 1`, a pure `Nat` identity), and the
  identification is the value-preserving `Fin.cast`: reading `pinFam`'s coordinates through it
  reads the coordinates of `f`.  Hence

    `famGraph (pinFam p n f) = h ▸ famGraph f`   (`famGraph_pinFam_eq`),

  for `h : p + (n+1) + 1 = (p+1) + n + 1`, and since `Ω`-membership is invariant under transport
  of the ambient dimension along an equality (`Work.WilG0.Omega_cast`) the `Ω`-bound of
  `famGraph (pinFam p n f)` is *exactly* that of `famGraph f`.

  This is the cost-free counterpart of `Work.WilkG4c.padFam_famGraph_mem`: `padFam` appends an
  extra dummy cube coordinate, so its layout is genuinely one dimension larger and the transfer
  pays constants; `pinFam` merely relabels coordinates, so nothing is paid.
-/
import Mathlib
import Submission.Work.WilG4c.SlicePinnedDefs
import Submission.Work.WilG0.Omega_cast

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Membership in a transported set -/

/-- Reading a point of `ℝ^b` in the transport of a set of `ℝ^a` along `h : a = b` is composing
with the value-preserving bijection `Fin.cast h`. -/
private theorem mem_transport_finCast {a b : ℕ} (h : a = b) (X : Set (Fin a → ℝ))
    (w : Fin b → ℝ) :
    w ∈ (h ▸ X) ↔ (fun i : Fin a => w (Fin.cast h i)) ∈ X := by
  cases h
  simp only [Fin.cast_refl, id_eq]

/-! ## 2. The graph of the pinned family -/

/-- `famGraph (pinFam p n f)` is the transport of `famGraph f` along the equality of ambient
dimensions `p + (n+1) + 1 = (p+1) + n + 1`: `pinFam` moves the distinguished cube coordinate
into the parameter block, which is a relabelling of the coordinates, not a change of dimension. -/
theorem famGraph_pinFam_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (h : p + (n + 1) + 1 = (p + 1) + n + 1) :
    WilkiesDesign.CG.famGraph (pinFam p n f) = h ▸ WilkiesDesign.CG.famGraph f := by
  ext w
  rw [mem_transport_finCast]
  simp only [WilkiesDesign.CG.famGraph, WilkiesDesign.graphOf, Set.mem_ofPred_eq, Fin.init,
    pinFam_apply]
  -- the value coordinate
  have hlast : Fin.cast h (Fin.last (p + (n + 1))) = Fin.last (p + 1 + n) := by
    apply Fin.ext
    simp
  -- the parameter coordinates `l`
  have hA : (fun i : Fin p => w (Fin.cast h (Fin.castAdd (n + 1) i).castSucc))
      = (fun i : Fin p => w (Fin.castAdd n i.castSucc).castSucc) := by
    funext i
    congr 1
  -- the cube coordinates `y`: `Fin.cons` (with `x` in the parameter block) versus `Fin.natAdd`
  have hB : (fun j : Fin (n + 1) => w (Fin.cast h (Fin.natAdd p j).castSucc))
      = Fin.cons (w (Fin.castAdd n (Fin.last p)).castSucc)
          (fun j : Fin n => w (Fin.natAdd (p + 1) j).castSucc) := by
    funext j
    induction j using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      congr 1
    | succ k =>
      rw [Fin.cons_succ]
      congr 1
      apply Fin.ext
      simp [Fin.val_natAdd, Fin.val_succ]
      omega
  rw [hlast, hA, hB]

/-! ## 3. The main lemma -/

theorem pinFam_famGraph_mem (S : WilkiesDesign.SOMin) (p n F0 D : ℕ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
    WilkiesDesign.CG.famGraph (Work.WilkG4c.pinFam p n f) ∈ S.Ω F0 D ((p + 1) + n + 1) := by
  intro hf
  have hcast : p + (n + 1) + 1 = (p + 1) + n + 1 := by omega
  rw [famGraph_pinFam_eq p n f hcast]
  exact Work.WilG0.Omega_cast hcast hf

end Work.WilkG4c

/-! ## 4. The module-path spelling of the name

The module is `Submission.Work.WilG4c.pinFam_famGraph_mem`, so the lemma is also wanted under the
namespace `Work.WilG4c`; the two spellings are the same statement. -/

namespace Work.WilG4c

theorem pinFam_famGraph_mem (S : WilkiesDesign.SOMin) (p n F0 D : ℕ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
    WilkiesDesign.CG.famGraph (Work.WilkG4c.pinFam p n f) ∈ S.Ω F0 D ((p + 1) + n + 1) :=
  Work.WilkG4c.pinFam_famGraph_mem S p n F0 D f

end Work.WilG4c
