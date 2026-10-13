/-
  Area G4b: `projCoords_mem` — the *coordinate image* of an `Ω`-set.

  For `X ⊆ ℝ^m` and `e : Fin N → Fin m`, the set `{y : Fin N → ℝ | ∃ x ∈ X, y = x ∘ e}`
  is the image of `X` under the coordinate projection `x ↦ x ∘ e : ℝ^m → ℝ^N`.  The
  proof builds the joint set of the pair `(y, x)` in `ℝ^{N+m}` — with the `y`-block in the
  first `N` coordinates and the `x`-block in the last `m` ones — as the intersection of

  * `lastBlk m N X`, the lift of `X` to the last `m` coordinates, and
  * `Work.WilG5.relSet e`, the polynomial relation `y j = x (e j)`;

  then `Work.WilG5.projN m` (forget the last `m` coordinates) produces exactly the image.
  The lift `lastBlk` is the `(N + m)`-framed version of `Work.WilG5.liftLast`, whose
  `Ω`-membership is transported across the equality `m + N = N + m` of the ambient
  dimensions by `reindexFin_mem`.
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic

set_option autoImplicit false

noncomputable section

namespace Work.WilG4b

open WilkiesDesign

/-! ## Auxiliary vocabulary -/

/-- `lastBlk m N X` is the set of `z : Fin (N + m) → ℝ` whose last `m` coordinates
(the block indexed by `Fin.natAdd N`) form a point of `X`.  This is the `(N + m)`-framed
form of `Work.WilG5.liftLast N X`, i.e. of the set produced by iterating `prod_left`. -/
def lastBlk (m N : ℕ) (X : Set (Fin m → ℝ)) : Set (Fin (N + m) → ℝ) :=
  {z | (fun i : Fin m => z (Fin.natAdd N i)) ∈ X}

/-- The transport of a set of functions `Fin a → ℝ` to functions `Fin b → ℝ` along an
equality `a = b` of the index sets: `z ↦ z ∘ Fin.cast h`. -/
def reindexFin {a b : ℕ} (h : a = b) (X : Set (Fin a → ℝ)) : Set (Fin b → ℝ) :=
  {z | z ∘ Fin.cast h ∈ X}

/-! ## Membership of the lifted block and of the transport -/

/-- `Ω`-membership is invariant under renaming the ambient dimension along `a = b`. -/
theorem reindexFin_mem {S : SOMin} {a b F D : ℕ} (h : a = b) {X : Set (Fin a → ℝ)}
    (hX : X ∈ S.Ω F D a) : reindexFin h X ∈ S.Ω F D b := by
  cases h
  simpa [reindexFin] using hX

/-- `lastBlk` is `liftLast` transported along `Nat.add_comm`. -/
theorem lastBlk_eq_reindexFin (m N : ℕ) (X : Set (Fin m → ℝ)) :
    lastBlk m N X = reindexFin (Nat.add_comm m N) (Work.WilG5.liftLast (n := m) N X) := by
  ext z
  have hfg : (fun i : Fin m => z (Fin.natAdd N i))
      = (fun i : Fin m => z (Fin.cast (Nat.add_comm m N) (Work.WilG5.lidx N i))) := by
    funext i
    exact congrArg z (Fin.ext (by rw [Fin.val_cast]; rfl))
  change ((fun i : Fin m => z (Fin.natAdd N i)) ∈ X)
    ↔ ((fun i : Fin m => z (Fin.cast (Nat.add_comm m N) (Work.WilG5.lidx N i))) ∈ X)
  rw [hfg]

/-- The lift of an `Ω`-set `X ⊆ ℝ^m` to the last `m` coordinates of `ℝ^{N + m}` is an
`Ω`-set, with format raised by the `N` new free coordinates. -/
theorem lastBlk_mem {S : SOMin} {m N F D : ℕ} {X : Set (Fin m → ℝ)}
    (hX : X ∈ S.Ω F D m) : lastBlk m N X ∈ S.Ω (F + N) D (N + m) := by
  have h1 : Work.WilG5.liftLast (n := m) N X ∈ S.Ω (F + N) D (m + N) :=
    Work.WilG5.liftLast_mem (S := S) N F D hX
  have h2 : reindexFin (Nat.add_comm m N) (Work.WilG5.liftLast (n := m) N X)
      ∈ S.Ω (F + N) D (N + m) :=
    reindexFin_mem (S := S) (Nat.add_comm m N) h1
  rw [lastBlk_eq_reindexFin]
  exact h2

/-! ## The image is a projection of the joint set -/

/-- Projecting the intersection of the lifted `X` and the relation set `y j = x (e j)`
along the last `m` coordinates yields the coordinate image of `X` under `x ↦ x ∘ e`. -/
theorem projN_lastBlk_rel (m N : ℕ) (e : Fin N → Fin m) (X : Set (Fin m → ℝ)) :
    Work.WilG5.projN m (lastBlk m N X ∩ Work.WilG5.relSet (p := N) (q := m) e)
      = {y : Fin N → ℝ | ∃ x : Fin m → ℝ, x ∈ X ∧ y = x ∘ e} := by
  ext u
  constructor
  · intro hu
    obtain ⟨w, hw⟩ := hu
    rw [Set.mem_inter_iff] at hw
    obtain ⟨hb, hr⟩ := hw
    refine ⟨w, ?_, ?_⟩
    · change (fun i : Fin m => Fin.append u w (Fin.natAdd N i)) ∈ X at hb
      have hfun : (fun i : Fin m => Fin.append u w (Fin.natAdd N i)) = w := by
        funext i; rw [Fin.append_right]
      rw [hfun] at hb
      exact hb
    · funext j
      have h := hr j
      rw [Fin.append_left, Fin.append_right] at h
      exact h
  · rintro ⟨w, hwX, rfl⟩
    refine ⟨w, ?_, ?_⟩
    · change (fun i : Fin m => Fin.append (w ∘ e) w (Fin.natAdd N i)) ∈ X
      have hfun : (fun i : Fin m => Fin.append (w ∘ e) w (Fin.natAdd N i)) = w := by
        funext i; rw [Fin.append_right]
      rw [hfun]
      exact hwX
    · intro j
      rw [Fin.append_left, Fin.append_right]
      rfl

/-! ## The main statement -/

theorem projCoords_mem (S : WilkiesDesign.SOMin) {m N : ℕ} (e : Fin N → Fin m) :
    ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (F D : ℕ) (X : Set (Fin m → ℝ)), X ∈ S.Ω F D m →
      {y : Fin N → ℝ | ∃ x : Fin m → ℝ, x ∈ X ∧ y = x ∘ e} ∈ S.Ω (F + K) (p.eval D) N := by
  refine ⟨N + (4 * (N + m) + 8) + 1 + m,
    Polynomial.C 2 * Polynomial.X + Polynomial.C (4 * N + 8), ?_⟩
  intro F D X hX
  have hblk0 : lastBlk m N X ∈ S.Ω (F + N) D (N + m) := lastBlk_mem (S := S) hX
  have hblk : lastBlk m N X ∈ S.Ω (F + (N + (4 * (N + m) + 8))) (D + (2 * N + 4)) (N + m) := by
    refine Work.WilG5.mem_mono hblk0 _ _ ?_ ?_ <;> omega
  have hrel0 : Work.WilG5.relSet (p := N) (q := m) e ∈
      S.Ω (4 * (N + m) + 8) (2 * N + 4) (N + m) :=
    Work.WilG5.relSet_mem (S := S) (p := N) (q := m) e
  have hrel : Work.WilG5.relSet (p := N) (q := m) e ∈
      S.Ω (F + (N + (4 * (N + m) + 8))) (D + (2 * N + 4)) (N + m) := by
    refine Work.WilG5.mem_mono hrel0 _ _ ?_ ?_ <;> omega
  have hJ := S.inter (fun _ : Fin 2 => D + (2 * N + 4))
    (fun i : Fin 2 => if i = 0 then lastBlk m N X else Work.WilG5.relSet (p := N) (q := m) e)
    (by intro i
        fin_cases i
        · simpa using hblk
        · simpa using hrel)
  rw [show (∑ _ : Fin 2, (D + (2 * N + 4))) = 2 * D + (4 * N + 8) from by
    rw [Fin.sum_univ_two]; ring] at hJ
  rw [show (⋂ i : Fin 2,
      (if i = 0 then lastBlk m N X else Work.WilG5.relSet (p := N) (q := m) e))
      = lastBlk m N X ∩ Work.WilG5.relSet (p := N) (q := m) e from by
    ext z; simp [Fin.forall_fin_two]] at hJ
  have hproj := Work.WilG5.projN_mem (S := S) (n := N) m _ _ hJ
  have hset := projN_lastBlk_rel (m := m) (N := N) e X
  rw [hset] at hproj
  have hp : (Polynomial.C 2 * Polynomial.X + Polynomial.C (4 * N + 8)).eval D
      = 2 * D + (4 * N + 8) := by simp
  rw [hp]
  refine Work.WilG5.mem_mono hproj _ _ ?_ le_rfl
  show F + (N + (4 * (N + m) + 8)) + 1 + m ≤ F + (N + (4 * (N + m) + 8) + 1 + m)
  omega

end Work.WilG4b
