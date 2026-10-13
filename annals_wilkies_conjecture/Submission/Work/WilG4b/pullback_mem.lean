/-
  Area G4b: **coordinate pullback** of an `Ω`-set.

  Given a sharply o-minimal structure `S` and a map `e : Fin m → Fin N`, the preimage
  `{z : Fin N → ℝ | z ∘ e ∈ X}` of an `Ω`-set `X ⊆ ℝ^m` is again an `Ω`-set, with a format
  increased by a constant `K` (depending only on `m, N`) and a degree bounded by a polynomial
  in the degree budget `D` of `X`.

  The construction is uniform in `m, N` (no case distinction on which is larger).  Passing to
  the joint space `ℝ^{N+m}`, whose first `N` coordinates carry a *fresh* point `z` and whose
  last `m` coordinates carry a point `w ∈ ℝ^m`, we form

      J = { (z,w) | w ∈ X and w j = z (e j) for all j : Fin m } .

  This is the intersection of
    * the lift of `X` to the last `m` coordinates (`liftLastM`, a `prod_left`-iteration), and
    * the polynomial relation set `relSetSwap e` (the `Ω`-analogue of the graph of `e`),

  and forgetting the last `m` coordinates (`projN`) turns it into the desired pullback:
  the fibre over `z` is `{w | w ∈ X, w = z ∘ e}`, nonempty exactly when `z ∘ e ∈ X`.

  The only index bookkeeping is that `liftLast` naturally produces a set in `Fin (m + N)`
  while the relation set lives in `Fin (N + m)`; this is handled once and for all by
  `Omega_cast` / `mem_transport`.
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture
open Work.WilG5

/-! ## 0. Transport along an equality of ambient dimensions -/

/-- `Ω`-membership is invariant under transport of the ambient dimension along an equality. -/
theorem Omega_cast {S : SOMin} {a b F D : ℕ} (h : a = b) {X : Set (Fin a → ℝ)}
    (hX : X ∈ S.Ω F D a) : (h ▸ X) ∈ S.Ω F D b := by
  cases h; exact hX

/-- Membership in a transported set: reading a point of `ℝ^b` in the transported set of a
set of `ℝ^a` amounts to composing with `Fin.cast h`. -/
theorem mem_transport {a b : ℕ} (h : a = b) (A : Set (Fin a → ℝ)) (v : Fin b → ℝ) :
    v ∈ (h ▸ A) ↔ (v ∘ Fin.cast h) ∈ A := by
  cases h; simp

/-! ## 1. Lifting a set to the last coordinates -/

/-- `X` placed on the last `m` coordinates of `ℝ^{N+m}` (the first `N` coordinates are free).
This is the shape produced by iterating `SOMin.prod_left`. -/
def liftLastM (m N : ℕ) (X : Set (Fin m → ℝ)) : Set (Fin (N + m) → ℝ) :=
  {v | (fun j : Fin m => v (Fin.natAdd N j)) ∈ X}

/-- The lift of an `Ω`-set to the last `m` coordinates of `ℝ^{N+m}` is an `Ω`-set; the format
grows by `N` (one `prod_left` per prepended coordinate) and the degree is unchanged. -/
theorem liftLastM_mem {S : SOMin} {m N F D : ℕ} {X : Set (Fin m → ℝ)}
    (hX : X ∈ S.Ω F D m) : liftLastM m N X ∈ S.Ω (F + N) D (N + m) := by
  have h := liftLast_mem (S := S) (n := m) N F D hX
  have hcast := Omega_cast (S := S) (Nat.add_comm m N) h
  have hset : ((Nat.add_comm m N) ▸ (liftLast (n := m) N X)) = liftLastM m N X := by
    ext v
    rw [mem_transport]
    have hfun : (fun i : Fin m => (v ∘ Fin.cast (Nat.add_comm m N)) (lidx N i))
        = (fun j : Fin m => v (Fin.natAdd N j)) := by
      funext i; simp [Function.comp_apply, lidx, Fin.natAdd]
    simp only [liftLastM, liftLast, Set.mem_ofPred_eq]
    rw [hfun]
  rwa [hset] at hcast

/-! ## 2. The joint set and its projection -/

/-- Forgetting the last `m` coordinates of the joint set
`{(z,w) | w ∈ X, w = z ∘ e}` returns the pullback `{z | z ∘ e ∈ X}`. -/
theorem projN_liftLastM_relSetSwap {m N : ℕ} (e : Fin m → Fin N) (X : Set (Fin m → ℝ)) :
    projN m (liftLastM m N X ∩ relSetSwap e) = {z : Fin N → ℝ | z ∘ e ∈ X} := by
  ext x
  constructor
  · rintro ⟨y, hy, hrel⟩
    have hyX : y ∈ X := by
      have h1 : (fun j : Fin m => Fin.append x y (Fin.natAdd N j)) = y := by
        funext j; rw [Fin.append_right]
      rw [liftLastM, Set.mem_ofPred_eq, h1] at hy
      exact hy
    have hyx : y = x ∘ e := by
      funext j
      have h2 : Fin.append x y (Fin.natAdd N j) = Fin.append x y (Fin.castAdd m (e j)) := hrel j
      rw [Fin.append_right, Fin.append_left] at h2
      exact h2
    show x ∘ e ∈ X
    rw [← hyx]; exact hyX
  · intro hx
    refine ⟨x ∘ e, ?_, ?_⟩
    · have h1 : (fun j : Fin m => Fin.append x (x ∘ e) (Fin.natAdd N j)) = (x ∘ e) := by
        funext j; rw [Fin.append_right]
      rw [liftLastM, Set.mem_ofPred_eq, h1]
      exact hx
    · intro j
      rw [Fin.append_right, Fin.append_left]
      rfl

/-! ## 3. The pullback is an `Ω`-set -/

theorem pullback_mem (S : WilkiesDesign.SOMin) {m N : ℕ} (e : Fin m → Fin N) :
    ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (F D : ℕ) (X : Set (Fin m → ℝ)), X ∈ S.Ω F D m →
      {z : Fin N → ℝ | z ∘ e ∈ X} ∈ S.Ω (F + K) (p.eval D) N := by
  refine ⟨max N (4 * (m + N) + 8) + 1 + m, Polynomial.X + Polynomial.C (2 * m + 4), ?_⟩
  intro F D X hX
  have hLift : liftLastM m N X ∈ S.Ω (F + N) D (N + m) := liftLastM_mem hX
  have hRel : relSetSwap e ∈ S.Ω (4 * (m + N) + 8) (2 * m + 4) (N + m) := relSetSwap_mem e
  have hJ : liftLastM m N X ∩ relSetSwap e ∈
      S.Ω (max (F + N) (4 * (m + N) + 8) + 1) (D + (2 * m + 4)) (N + m) := by
    have h2 := S.inter (F := max (F + N) (4 * (m + N) + 8)) (n := N + m) (k := 2)
      (fun i : Fin 2 => if i = 0 then D else 2 * m + 4)
      (fun i : Fin 2 => if i = 0 then liftLastM m N X else relSetSwap e)
      (by intro i
          fin_cases i
          · simpa using (mem_mono hLift (max (F + N) (4 * (m + N) + 8)) D (le_max_left _ _) le_rfl)
          · simpa using (mem_mono hRel (max (F + N) (4 * (m + N) + 8)) (2 * m + 4) (le_max_right _ _) le_rfl))
    rw [show (∑ i : Fin 2, (if i = 0 then D else 2 * m + 4)) = D + (2 * m + 4) from by
      simp [Fin.sum_univ_two]] at h2
    rwa [Work.WilG1.Omega.iInter_fin_two] at h2
  have hproj := projN_mem (S := S) (n := N) m (max (F + N) (4 * (m + N) + 8) + 1) (D + (2 * m + 4)) hJ
  rw [projN_liftLastM_relSetSwap e X] at hproj
  refine mem_mono hproj (F + (max N (4 * (m + N) + 8) + 1 + m))
    ((Polynomial.X + Polynomial.C (2 * m + 4)).eval D) ?_ ?_
  · omega
  · simp [Polynomial.eval_add]

end Work.WilG4b
