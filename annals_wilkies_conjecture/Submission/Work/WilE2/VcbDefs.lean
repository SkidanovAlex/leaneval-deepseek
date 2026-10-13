/-
  Work.WilE2 — area E2.  Shared vocabulary for `variety_components_bound` (GV Corollary 3.3).

  This module isolates the definitions and the small bookkeeping lemmas that both the main
  theorem (`variety_components_bound`) and the geometric input it rests on (the bound for the
  components of a Pfaffian variety inside a *ball*, `ballComponentsBound`) use.

  * `Zset c g` — the zero set `{x | ∀ f ∈ g, eaEval c f x = 0}` of a finite family of EA
    polynomials on the fixed chain `c`.
  * `Xset c g` — that zero set cut by the cube `cubeC k`.
  * `Hits X s` — `s ⊆ X` hits every connected component of `X`.
  * `KhoBound` — the Khovanskii hypothesis `E2a` (non-degenerate zeros of a square EA system
    are polynomially bounded).
  * `SardDense` — the rectangular Sard hypothesis (`regular_values_dense`).
  * `coverBound_hits` / `hits_coverBound` — a set is hit by `N` points iff it is covered by `N`
    preconnected pieces; this is the bridge between "the number of components is `≤ N`" and the
    hitting-set formulation.
-/
import Mathlib
import Submission.Work.WilE2.ComponentsDefs

set_option autoImplicit false
noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E

/-- The zero set of a finite family `g` of EA polynomials on the chain `c`. -/
def Zset {k r : ℕ} (c : EAChain k r) (g : Finset (EAPoly k r)) : Set (Fin k → ℝ) :=
  {x | ∀ f ∈ g, eaEval c f x = 0}

/-- The zero set cut by the cube. -/
def Xset {k r : ℕ} (c : EAChain k r) (g : Finset (EAPoly k r)) : Set (Fin k → ℝ) :=
  cubeC k ∩ Zset c g

/-- `s` (a finite set of points of `X`) hits every connected component of `X`. -/
def Hits {k : ℕ} (X : Set (Fin k → ℝ)) (s : Finset (Fin k → ℝ)) : Prop :=
  ∀ x ∈ X, ∃ y ∈ s, connectedComponentIn X x = connectedComponentIn X y

/-- `X` is covered by at most `N` nonempty preconnected subsets of `X`.  This is equivalent to
"`X` has at most `N` connected components" and is the form in which the counting arguments
below produce the bound. -/
def CoverBound {k : ℕ} (X : Set (Fin k → ℝ)) (N : ℕ) : Prop :=
  ∃ A : Finset (Set (Fin k → ℝ)), A.card ≤ N ∧
    (∀ B ∈ A, B ⊆ X ∧ B.Nonempty ∧ IsPreconnected B) ∧
    X ⊆ ⋃₀ (A : Set (Set (Fin k → ℝ)))

/-- **The Khovanskii hypothesis `E2a`.**  For every format bound there is a polynomial such that
any finite set of non-degenerate zeros of a square EA system in at most that format has that
many elements. -/
def KhoBound : Prop := ∀ F : ℕ, ∃ p : Polynomial ℕ,
  ∀ (k r : ℕ) (c : EAChain k r) (f : Fin k → EAPoly k r) (s : Finset (Fin k → ℝ)), k + r ≤ F →
    (∀ x ∈ s, (∀ i, eaEval c (f i) x = 0) ∧
      (Matrix.of fun i j => eaEval c (eaD c j (f i)) x).det ≠ 0) →
    s.card ≤ p.eval (∑ i, atomDeg (f i))

/-- **The rectangular Sard hypothesis.**  Regular values of a `C²` map `ℝ^{m+1} → ℝ^m` are
dense. -/
def SardDense : Prop := ∀ (m : ℕ) (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)), ContDiff ℝ 2 G →
  ∀ (y₀ : Fin m → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin m → ℝ, dist y y₀ < ε ∧
    ∀ z, G z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => G w a) z)

/-- **A cover by `N` preconnected pieces yields a hitting set of `N` points.**  Every piece
contains a point, and every component of `X` contains at least one whole piece, so the chosen
points hit every component. -/
theorem coverBound_hits {k : ℕ} {X : Set (Fin k → ℝ)} {N : ℕ}
    (h : CoverBound X N) :
    ∃ s : Finset (Fin k → ℝ), (↑s : Set (Fin k → ℝ)) ⊆ X ∧ s.card ≤ N ∧ Hits X s := by
  obtain ⟨A, hAcard, hA, hcov⟩ := h
  refine ⟨A.attach.image (fun B => Classical.choose (hA B.1 B.2).2.1), ?_, ?_, ?_⟩
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_attach, true_and] at hy
    obtain ⟨B, rfl⟩ := hy
    exact (hA B.1 B.2).1 (Classical.choose_spec (hA B.1 B.2).2.1)
  · refine le_trans (Finset.card_image_le) ?_
    simp only [Finset.card_attach]
    exact hAcard
  · intro x hx
    obtain ⟨B, hBA, hxB⟩ := hcov hx
    obtain ⟨hBX, hBne, hBpc⟩ := hA B hBA
    refine ⟨Classical.choose hBne, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨B, hBA⟩, Finset.mem_attach _ _, rfl⟩
    · exact (connectedComponentIn_eq
        ((hBpc.subset_connectedComponentIn (Classical.choose_spec hBne) hBX) hxB)).symm

/-- **A hitting set by `N` points yields a cover by `N` preconnected pieces** (the components of
the hitting points). -/
theorem hits_coverBound {k : ℕ} {X : Set (Fin k → ℝ)} {s : Finset (Fin k → ℝ)}
    (hs : (↑s : Set (Fin k → ℝ)) ⊆ X) (h : Hits X s) : CoverBound X s.card := by
  refine ⟨(s.filter (fun y => y ∈ X)).image (fun y => connectedComponentIn X y), ?_, ?_, ?_⟩
  · exact le_trans Finset.card_image_le (Finset.card_filter_le _ _)
  · intro B hB
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨connectedComponentIn_subset X y,
      ⟨y, mem_connectedComponentIn (Finset.mem_filter.mp hy).2⟩,
      isPreconnected_connectedComponentIn⟩
  · intro x hx
    obtain ⟨y, hys, hy⟩ := h x hx
    refine ⟨connectedComponentIn X y, Finset.mem_image.mpr ⟨y, ?_, rfl⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hys, hs hys⟩
    · rw [← hy]; exact mem_connectedComponentIn hx

end Work.WilE2
