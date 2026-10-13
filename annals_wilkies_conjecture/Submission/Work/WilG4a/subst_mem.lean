/-
  WilG4a : the substitution atom of the Ω-calculus.

  The target `Work.WilG4a.subst_mem` says that pulling back an `Ω F D m`-set along a
  coordinate map `ι : Fin m → Fin n` produces an `Ω`-set of dimension `n` whose format grows
  by `2 * (n + m) + 1` and whose degree grows by `2`.  The `+2` is the charge for a single
  substitution atom, realised by the polynomial `Σ_j (W_j - X_{ι j})²` (`WilG0.diagPoly`).

  The proof has three ingredients, each proved in a sibling module of this directory:

  * `Work.WilG0.liftNM n m A` is `A` placed in the last `m` coordinates of `ℝ^{n+m}`; it is
    obtained by iterating `SOMin.prod_left` `n` times (`liftNM_mem`).
  * `Work.WilG0.diagSet n m ι` is the graph of `x ↦ x ∘ ι` inside `ℝ^{n+m}`; it is the zero
    set of the degree-`2` polynomial `diagPoly` (`diagSet_mem`).
  * The pullback of `A` along `ι` is exactly the projection (`projLastIter`) of the
    intersection `liftNM n m A ∩ diagSet n m ι` (`subst_lift_eq`).

  This file supplies the `Ω`-bookkeeping: monotonicity `mem_mono`, the iterated projection
  `projLastIter_mem`, and the assembly.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG0.Defs
import Submission.Work.WilG4a.liftNM_mem
import Submission.Work.WilG4a.diagSet_mem
import Submission.Work.WilG4a.subst_lift_eq

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign
open Work.WilG0

variable {S : WilkiesDesign.SOMin}

/-! ## Monotonicity of the format and degree indices -/

/-- A membership `X ∈ S.Ω F D n` may be raised to any larger format and degree. -/
theorem mem_mono {F D F' D' n : ℕ} {X : Set (Fin n → ℝ)} (h : X ∈ S.Ω F D n)
    (hF : F ≤ F') (hD : D ≤ D') : X ∈ S.Ω F' D' n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hF
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hD
  have hk : ∀ k, X ∈ S.Ω (F + k) D n := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih => simpa [Nat.add_assoc] using S.mono_F ih
  have hl : ∀ l, X ∈ S.Ω (F + k) (D + l) n := by
    intro l
    induction l with
    | zero => simpa using hk k
    | succ l ih => simpa [Nat.add_assoc] using S.mono_D ih
  exact hl l

/-! ## The iterated projection `projLastIter` -/

/-- `projLastIter n m X` — the result of applying `SOMin.proj` (forget the last coordinate)
`m` times — costs `m` in the format and nothing in the degree. -/
theorem projLastIter_mem {D n m : ℕ} : ∀ {F : ℕ} {X : Set (Fin (n + m) → ℝ)},
    X ∈ S.Ω F D (n + m) → projLastIter n m X ∈ S.Ω (F + m) D n := by
  induction m with
  | zero => intro F X hX; simpa [projLastIter] using hX
  | succ m ih =>
    intro F X hX
    rw [show projLastIter n (m + 1) X = projLastIter n m (projLast X) from rfl]
    have h1 : projLast X ∈ S.Ω (F + 1) D (n + m) := S.proj hX
    exact mem_mono (ih h1) (by omega) le_rfl

/-! ## A `Fin 2`-indexed intersection is a binary intersection -/

theorem iInter_fin_two {α : Type*} (X Y : Set α) :
    Set.iInter (fun i : Fin 2 => if i = 0 then X else Y) = X ∩ Y := by
  ext z
  rw [Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro hh
    exact ⟨by simpa using hh 0, by simpa using hh 1⟩
  · rintro ⟨hx, hy⟩ i
    fin_cases i
    · simpa using hx
    · simpa using hy

/-! ## The substitution atom -/

/-- **Substitution.**  Pulling back an `Ω F D m`-set along a coordinate map
`ι : Fin m → Fin n` yields an `Ω`-set of dimension `n`, format at most `F + 2 * (n + m) + 1`
and degree at most `D + 2`.

The set is the projection of `liftNM n m A ∩ diagSet n m ι`, an intersection of the lifted
set (format `F + n`, degree `D`) with the degree-`2` graph of `x ↦ x ∘ ι`; the intersection
costs one format step and `2` in the degree, and the `m` projections out of the last
coordinates cost `m` in the format.  The format is bounded by
`max (F + n) (n + m) + 1 + m ≤ F + 2 * (n + m) + 1`. -/
theorem subst_mem (S : WilkiesDesign.SOMin) {m n : ℕ} (ι : Fin m → Fin n) {F D : ℕ} {A : Set (Fin m → ℝ)} (hA : A ∈ S.Ω F D m) : {x : Fin n → ℝ | x ∘ ι ∈ A} ∈ S.Ω (F + 2 * (n + m) + 1) (D + 2) n := by
  have hlift : liftNM n m A ∈ S.Ω (F + n) D (n + m) := liftNM_mem S hA n
  have hdiag : diagSet n m ι ∈ S.Ω (n + m) 2 (n + m) := diagSet_mem S n m ι
  have h1 : liftNM n m A ∈ S.Ω (max (F + n) (n + m)) D (n + m) :=
    mem_mono hlift (le_max_left _ _) le_rfl
  have h2 : diagSet n m ι ∈ S.Ω (max (F + n) (n + m)) 2 (n + m) :=
    mem_mono hdiag (le_max_right _ _) le_rfl
  have h3 : (liftNM n m A ∩ diagSet n m ι) ∈
      S.Ω (max (F + n) (n + m) + 1) (D + 2) (n + m) := by
    have h := S.inter (fun i : Fin 2 => if i = 0 then D else 2)
      (fun i : Fin 2 => if i = 0 then liftNM n m A else diagSet n m ι)
      (by intro i; fin_cases i
          · simpa using h1
          · simpa using h2)
    have hsum : (∑ i : Fin 2, (if i = 0 then D else 2)) = D + 2 := by
      rw [Fin.sum_univ_two]; norm_num
    rw [hsum] at h
    rwa [iInter_fin_two] at h
  have h4 : projLastIter n m (liftNM n m A ∩ diagSet n m ι) ∈
      S.Ω (max (F + n) (n + m) + 1 + m) (D + 2) n := projLastIter_mem h3
  have hmax : max (F + n) (n + m) ≤ F + n + m := max_le (by omega) (by omega)
  have h5 : projLastIter n m (liftNM n m A ∩ diagSet n m ι) ∈
      S.Ω (F + 2 * (n + m) + 1) (D + 2) n := mem_mono h4 (by omega) le_rfl
  rw [subst_lift_eq]
  exact h5

end Work.WilG4a
