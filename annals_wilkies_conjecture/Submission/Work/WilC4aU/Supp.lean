/-
  Area C4aU: the `x`-support of a rexp-existential family, used to produce the pairs
  `(x, 2 x)` needed to show that `2 ^ q` is a cluster value of the ratio `f (2 x) / f x`.

  `XSupp Y` is the set of `(x, c)` such that the fibre `Y_c` has a point above `x`.  It is
  existentially definable (`xSupp_rexExist`), so uniform finiteness applies to it; together with
  the fact that preconnected subsets of `ℝ` are intervals this shows that the `x`-support of a
  fibre with `¬ ZeroSect` contains a half line `[b, ∞)`.
-/
import Submission.Work.WilC4aU.Defs

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Classical Topology
namespace Work.WilC4aU

open WilkiesDesign (RExpExist)
open Work.WilC0

/-- The coordinate permutation reading the tuple `(x, c₀, …, c_{k-1}, y)` as the tuple
`(x, y, c₀, …, c_{k-1})` in the coordinate order of `Y` (`0 ↦ 0`, `1 ↦ k + 1`,
`i + 2 ↦ i + 1`). -/
def putYLast (k : ℕ) : Fin (k + 2) → Fin (k + 2) :=
  Fin.cases 0 (Fin.cases (Fin.last (k + 1)) (fun i : Fin k => Fin.castSucc (Fin.succ i)))

@[simp] theorem putYLast_zero (k : ℕ) : putYLast k 0 = 0 := by
  rw [putYLast, Fin.cases_zero]

theorem putYLast_one (k : ℕ) : putYLast k (Fin.succ (0 : Fin (k + 1))) = Fin.last (k + 1) := by
  rw [putYLast, Fin.cases_succ, Fin.cases_zero]

theorem putYLast_succ_succ (k : ℕ) (i : Fin k) :
    putYLast k (Fin.succ (Fin.succ i)) = Fin.castSucc (Fin.succ i) := by
  rw [putYLast, Fin.cases_succ, Fin.cases_succ]

/-- The `x`-support of `Y` over all parameters: `{(x, c) | ∃ y, (x, y, c) ∈ Y}`, written in the
coordinate order `(x, c₀, …, c_{k-1})`. -/
def XSupp {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {z | ∃ a : ℝ, (Fin.snoc z a : Fin (k + 2) → ℝ) ∘ putYLast k ∈ Y}

/-- Existential quantification over the last coordinate, in `Fin.snoc` form. -/
theorem rexExistI_existsSnoc {n : ℕ} {X : Set (Fin (n + 1) → ℝ)} (hX : RExpExistI X) :
    RExpExistI {z : Fin n → ℝ | ∃ a : ℝ, Fin.snoc z a ∈ X} := by
  refine (rexExistI_existsFin hX).of_eq ?_
  ext z
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rwa [Fin.append_right_eq_snoc] at ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rwa [Fin.append_right_eq_snoc]⟩

/-- The composition identity behind the fibre description of `XSupp`. -/
theorem snoc_cons_comp_putYLast {k : ℕ} (x y : ℝ) (c : Fin k → ℝ) :
    ((Fin.snoc (Fin.cons x c) y : Fin (k + 2) → ℝ)) ∘ putYLast k = Fin.cons x (Fin.cons y c) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · show (Fin.snoc (Fin.cons x c) y : Fin (k + 2) → ℝ) (putYLast k 0) = _
    rw [putYLast_zero, Fin.snoc_apply_zero, Fin.cons_zero, Fin.cons_zero]
  · intro j
    refine Fin.cases ?_ ?_ j
    · have hidx : putYLast k (Fin.succ (0 : Fin (k + 1))) = Fin.last (k + 1) := putYLast_one k
      show (Fin.snoc (Fin.cons x c) y : Fin (k + 2) → ℝ) (putYLast k (Fin.succ 0)) = _
      rw [hidx, Fin.snoc_last, Fin.cons_succ, Fin.cons_zero]
    · intro i
      have hidx : putYLast k (Fin.succ (Fin.succ i)) = Fin.castSucc (Fin.succ i) :=
        putYLast_succ_succ k i
      show (Fin.snoc (Fin.cons x c) y : Fin (k + 2) → ℝ)
        (putYLast k (Fin.succ (Fin.succ i))) = _
      rw [hidx, Fin.snoc_castSucc, Fin.cons_succ]
      simp only [Fin.cons_succ]

/-- The fibre of `XSupp Y` at `c` is the `x`-support of the fibre of `Y` at `c`. -/
theorem cons_mem_xSupp {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x : ℝ} :
    Fin.cons x c ∈ XSupp Y ↔ ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rwa [snoc_cons_comp_putYLast] at ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rwa [snoc_cons_comp_putYLast]⟩

/-- `XSupp Y` is existentially definable when `Y` is. -/
theorem xSupp_rexExist {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} (hY : RExpExist Y) :
    RExpExist (XSupp Y) := by
  have h1 : RExpExistI Y := (rexExistI_iff_rexExist Y).mpr hY
  have h2 : RExpExistI {v : Fin (k + 2) → ℝ | v ∘ putYLast k ∈ Y} :=
    h1.pullback (putYLast k)
  have h3 : RExpExistI (XSupp Y) := rexExistI_existsSnoc h2
  exact (rexExistI_iff_rexExist (XSupp Y)).mp h3

end Work.WilC4aU
