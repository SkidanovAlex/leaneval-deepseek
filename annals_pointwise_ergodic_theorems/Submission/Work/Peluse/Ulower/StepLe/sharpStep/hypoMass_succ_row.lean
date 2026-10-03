import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.cubeTerm_mean_cons

/-!
# The row decomposition of the hypothesis mass

This file proves the row form of the dimension step of the sharp (density-free) dual--difference
interchange: the hypothesis mass at level `σ+1` is the sum, over the pairs `(a,b) ∈ [1,D]²` of
first coordinates, of the hypothesis masses of the level-`σ` *row families*

`K^{(a,b)}_{(z,z')}(y) = G z (y + b) · conj (G z' (y + a))`

over `Z × Z`, tested against the row fibre `rowFibre σ D H a b` and the row phases
`(u,v) ↦ φ (cons a u) (cons b v)`.

The mathematical content is the identity `cubeTerm_mean_cons` (the cube term of the averaged
function is the averaged cube term of the bilinear expression) combined with the bookkeeping that
splits the set `H` of shift pairs according to its first coordinates; the latter is the auxiliary
combinatorial lemma `sum_H_eq_sum_rows`.
-/

open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe.sharpStep

open Finset

/-- The map `((a,b),(p,q)) ↦ ((a :: p), (b :: q))`, gluing a pair of first coordinates
(`Fin 1 → ℤ`, i.e. a single integer) to a pair of level-`σ` shifts.  This is the index map of the
row decomposition of `H`. -/
private def succRowMap (σ : ℕ)
    (x : ((Fin 1 → ℤ) × (Fin 1 → ℤ)) × ((Fin σ → ℤ) × (Fin σ → ℤ))) :
    (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) :=
  (Fin.cons (x.1.1 0) x.2.1, Fin.cons (x.1.2 0) x.2.2)

/-- **Row decomposition of a sum over `H`.**  A sum over a set `H` of level-`(σ+1)` shift pairs whose
coordinates all lie in `[1,D]` can be computed by summing over the pairs of *first* coordinates
`(a,b) ∈ [1,D]²` and then over the corresponding row fibre. -/
private lemma sum_H_eq_sum_rows {σ D : ℕ}
    (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    (hcoords : ∀ p ∈ H, ∀ i : Fin (σ+1),
      p.1 i ∈ Finset.Icc (1:ℤ) (D:ℤ) ∧ p.2 i ∈ Finset.Icc (1:ℤ) (D:ℤ))
    {M : Type} [AddCommMonoid M]
    (G0 : (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) → M) :
    ∑ p ∈ H, G0 p
      = ∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
          ∑ p ∈ Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0),
            G0 (Fin.cons (ab.1 0) p.1, Fin.cons (ab.2 0) p.2) := by
  classical
  have hA : (∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
          ∑ p ∈ Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0),
            G0 (Fin.cons (ab.1 0) p.1, Fin.cons (ab.2 0) p.2))
      = ∑ x ∈ ((Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D) ×ˢ
          (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D)).filter
          (fun x => succRowMap σ x ∈ H), G0 (succRowMap σ x) := by
    simp only [Work.Peluse.Ulower.StepLe.rowFibre, Finset.sum_filter]
    conv_rhs => rw [Finset.sum_product]
    rfl
  rw [hA]
  refine (Finset.sum_bij
    (s := ((Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D) ×ˢ
        (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D)).filter
        (fun x => succRowMap σ x ∈ H))
    (t := H) (f := fun x => G0 (succRowMap σ x)) (g := G0)
    (fun x _ => succRowMap σ x) ?_ ?_ ?_ ?_).symm
  · -- the image lies in `H`
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  · -- injectivity of the gluing map
    intro x hx y hy hxy
    simp only [succRowMap, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have e1 : x.1.1 0 = y.1.1 0 := by
      have := congr_fun h1 0; simpa using this
    have e2 : x.2.1 = y.2.1 := by
      funext i; have := congr_fun h1 i.succ; simpa using this
    have e3 : x.1.2 0 = y.1.2 0 := by
      have := congr_fun h2 0; simpa using this
    have e4 : x.2.2 = y.2.2 := by
      funext i; have := congr_fun h2 i.succ; simpa using this
    have f1 : x.1.1 = y.1.1 := by funext i; rw [Subsingleton.elim i 0]; exact e1
    have f2 : x.1.2 = y.1.2 := by funext i; rw [Subsingleton.elim i 0]; exact e3
    exact Prod.ext (Prod.ext f1 f2) (Prod.ext e2 e4)
  · -- surjectivity onto `H`
    intro q hq
    refine ⟨⟨(fun _ => q.1 0, fun _ => q.2 0), (Fin.tail q.1, Fin.tail q.2)⟩, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · exact Work.Peluse.Ulower.mem_thetaBox.mpr (fun i => by simpa using (hcoords q hq 0).1)
        · exact Work.Peluse.Ulower.mem_thetaBox.mpr (fun i => by simpa using (hcoords q hq 0).2)
      · refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · refine Work.Peluse.Ulower.mem_thetaBox.mpr (fun i => Finset.mem_Icc.mpr ?_)
          exact ⟨(Finset.mem_Icc.mp (hcoords q hq i.succ).1).1,
                 (Finset.mem_Icc.mp (hcoords q hq i.succ).1).2⟩
        · refine Work.Peluse.Ulower.mem_thetaBox.mpr (fun i => Finset.mem_Icc.mpr ?_)
          exact ⟨(Finset.mem_Icc.mp (hcoords q hq i.succ).2).1,
                 (Finset.mem_Icc.mp (hcoords q hq i.succ).2).2⟩
      · simpa [succRowMap, Fin.cons_self_tail] using hq
    · simp only [succRowMap, Fin.cons_self_tail]
  · intro a ha
    rfl

/-- **Row form of the dimension step of the sharp mass interchange.**  The hypothesis mass at level
`σ+1` splits, according to the first coordinates `(a,b) ∈ [1,D]²` of the shift pairs, as the sum of
the level-`σ` hypothesis masses of the row families over `Z × Z`. -/
theorem hypoMass_succ_row {σ D B : ℕ} {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    (φ : (Fin (σ+1) → ℤ) → (Fin (σ+1) → ℤ) → ℝ)
    (hcoords : ∀ p ∈ H, ∀ i : Fin (σ+1),
      p.1 i ∈ Finset.Icc (1:ℤ) (D:ℤ) ∧ p.2 i ∈ Finset.Icc (1:ℤ) (D:ℤ)) :
    Work.Peluse.Ulower.StepLe.hypoMass (σ+1) B G H φ
      = ∑ ab ∈ (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D),
          Work.Peluse.Ulower.StepLe.hypoMass σ B
            (fun p : Z × Z => fun y => G p.1 (y + ab.2 0) * star (G p.2 (y + ab.1 0)))
            (Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0))
            (fun u v => φ (Fin.cons (ab.1 0) u) (Fin.cons (ab.2 0) v)) := by
  simp only [Work.Peluse.Ulower.StepLe.hypoMass]
  rw [sum_H_eq_sum_rows H hcoords (fun q : (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) =>
      ‖((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm q.1 q.2
        (fun y => ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z y) x *
        Complex.exp (2 * Real.pi * Complex.I * (φ q.1 q.2 : ℂ) * (x : ℂ))‖ ^ 2)]
  refine Finset.sum_congr rfl (fun ab hab => Finset.sum_congr rfl (fun p hp => ?_))
  dsimp only
  simp only [Work.Peluse.Ulower.StepLe.ddiSharp.cubeTerm_mean_cons]

end Work.Peluse.Ulower.StepLe.sharpStep
