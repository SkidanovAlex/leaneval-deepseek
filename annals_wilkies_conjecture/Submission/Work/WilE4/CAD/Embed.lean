/-
  WilE4 / CAD — the embedding of the fibrewise-closure configuration into a single space, and the
  quadratic atom expressing `Σ_i (y'_i - y_i)^2 < ε^2`.

  Given `p, q`, the space `Fin (p + 2q + 1)` is organised as

      (x_0 … x_{p-1} | y_0 … y_{q-1} | ε | y'_0 … y'_{q-1}),

  * `SAd.renameAlong f` renames the variables of a DNF along a map of indices;
  * `posX`, `posY`, `posEps`, `posYp` are the four blocks of positions;
  * `fiberEmbed p q : Fin (p + q) → Fin (p + 2q + 1)` is the injection `(x, y') ↪ (x, y, ε, y')`
    along which the atoms of the input set are renamed (so that the last `q + 1` coordinates — the
    pair `(ε, y')` — are the ones that get projected out);
  * `quadAtom p q = Σ_i (y'_i - y_i)^2 - ε^2`.
-/
import Submission.Work.WilE4.CAD.Size

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilE4

open MvPolynomial Polynomial

namespace SAd

variable {m n : ℕ}

/-- Renaming the variables of a DNF along a map of indices. -/
def renameAlong (f : Fin m → Fin n) (X : SAd m) : SAd n :=
  ⟨X.basics.map fun B =>
    ⟨B.eqs.map (MvPolynomial.rename f), B.pos.map (MvPolynomial.rename f)⟩⟩

theorem renameAlong_set (f : Fin m → Fin n) (X : SAd m) :
    (X.renameAlong f).set = {z : Fin n → ℝ | (fun i => z (f i)) ∈ X.set} := by
  ext z
  constructor
  · rintro ⟨B, hB, hBz⟩
    simp only [renameAlong, List.mem_map] at hB
    obtain ⟨B₀, hB₀, rfl⟩ := hB
    refine ⟨B₀, hB₀, ?_, ?_⟩
    · intro P hP
      have h := hBz.1 (MvPolynomial.rename f P) (List.mem_map_of_mem hP)
      rwa [MvPolynomial.eval_rename] at h
    · intro P hP
      have h := hBz.2 (MvPolynomial.rename f P) (List.mem_map_of_mem hP)
      rwa [MvPolynomial.eval_rename] at h
  · rintro ⟨B, hB, hBz⟩
    refine ⟨⟨B.eqs.map (MvPolynomial.rename f), B.pos.map (MvPolynomial.rename f)⟩,
      List.mem_map_of_mem hB, ?_, ?_⟩
    · intro P hP
      obtain ⟨P₀, hP₀, rfl⟩ := List.mem_map.mp hP
      rw [MvPolynomial.eval_rename]
      exact hBz.1 P₀ hP₀
    · intro P hP
      obtain ⟨P₀, hP₀, rfl⟩ := List.mem_map.mp hP
      rw [MvPolynomial.eval_rename]
      exact hBz.2 P₀ hP₀

theorem renameAlong_deg_le (f : Fin m → Fin n) (X : SAd m) :
    (X.renameAlong f).deg ≤ X.deg := by
  have h : ∀ l : List (MvPolynomial (Fin m) ℝ),
      ((l.map (MvPolynomial.rename f)).map atomDegD).sum ≤ (l.map atomDegD).sum :=
    fun l => by
      rw [List.map_map]
      exact List.sum_le_sum fun P _ => CAD.atomDegD_rename_le f P
  show ((X.basics.map fun B : BasicD m =>
      (⟨B.eqs.map (MvPolynomial.rename f), B.pos.map (MvPolynomial.rename f)⟩ : BasicD n)).map
      BasicD.deg).sum ≤ (X.basics.map BasicD.deg).sum
  rw [List.map_map]
  refine List.sum_le_sum fun B _ => ?_
  show (⟨B.eqs.map (MvPolynomial.rename f), B.pos.map (MvPolynomial.rename f)⟩ : BasicD n).deg
    ≤ B.deg
  rw [BasicD.deg_cons, BasicD.deg_cons]
  exact add_le_add (h B.eqs) (h B.pos)

end SAd

end Work.WilE4

namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

variable {k m n : ℕ}

/-! ## The four blocks of coordinates -/

/-- The position of `x_i` in `Fin (p + 2q + 1)`. -/
def posX (p q : ℕ) (i : Fin p) : Fin (p + 2 * q + 1) := ⟨i.val, by omega⟩

/-- The position of `y_i` in `Fin (p + 2q + 1)`. -/
def posY (p q : ℕ) (i : Fin q) : Fin (p + 2 * q + 1) := ⟨p + i.val, by omega⟩

/-- The position of `ε` in `Fin (p + 2q + 1)`. -/
def posEps (p q : ℕ) : Fin (p + 2 * q + 1) := ⟨p + q, by omega⟩

/-- The position of `y'_i` in `Fin (p + 2q + 1)`. -/
def posYp (p q : ℕ) (i : Fin q) : Fin (p + 2 * q + 1) := ⟨p + q + 1 + i.val, by omega⟩

/-- The injection `(x, y') ↪ (x, y, ε, y')`: the atoms of the input set are renamed along it, so
that they see the coordinates `x` and `y'` of the big space. -/
def fiberEmbed (p q : ℕ) : Fin (p + q) → Fin (p + 2 * q + 1) :=
  fun i => if i.val < p then ⟨i.val, by omega⟩ else ⟨i.val + q + 1, by omega⟩

/-- The atom `Σ_i (y'_i - y_i)^2 - ε^2`, whose negativity is the condition `‖y' - y‖₂ < |ε|`. -/
def quadAtom (p q : ℕ) : MvPolynomial (Fin (p + 2 * q + 1)) ℝ :=
  ((Finset.univ : Finset (Fin q)).sum fun i =>
      (MvPolynomial.X (posYp p q i) - MvPolynomial.X (posY p q i)) ^ 2)
    - MvPolynomial.X (posEps p q) ^ 2

theorem eval_quadAtom (p q : ℕ) (z : Fin (p + 2 * q + 1) → ℝ) :
    MvPolynomial.eval z (quadAtom p q) =
      ((Finset.univ : Finset (Fin q)).sum fun i =>
          (z (posYp p q i) - z (posY p q i)) ^ 2) - z (posEps p q) ^ 2 := by
  simp [quadAtom]

theorem totalDegree_sq_le {m : ℕ} (P : MvPolynomial (Fin m) ℝ) :
    (P ^ 2).totalDegree ≤ 2 * P.totalDegree := by
  rw [pow_two]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

theorem atomDegD_quadAtom_le (p q : ℕ) : atomDegD (quadAtom p q) ≤ 3 := by
  have hX : ∀ i : Fin (p + 2 * q + 1),
      (MvPolynomial.X i : MvPolynomial (Fin (p + 2 * q + 1)) ℝ).totalDegree ≤ 1 :=
    fun i => le_of_eq (MvPolynomial.totalDegree_X i)
  have hterm : ∀ i : Fin q,
      (((MvPolynomial.X (posYp p q i) : MvPolynomial (Fin (p + 2 * q + 1)) ℝ) -
        MvPolynomial.X (posY p q i)) ^ 2).totalDegree ≤ 2 := by
    intro i
    refine (totalDegree_sq_le _).trans ?_
    have h1 : ((MvPolynomial.X (posYp p q i) : MvPolynomial (Fin (p + 2 * q + 1)) ℝ) -
        MvPolynomial.X (posY p q i)).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_sub _ _).trans (max_le (hX _) (hX _))
    omega
  have hsum : (((Finset.univ : Finset (Fin q)).sum fun i =>
      ((MvPolynomial.X (posYp p q i) : MvPolynomial (Fin (p + 2 * q + 1)) ℝ) -
        MvPolynomial.X (posY p q i)) ^ 2)).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => hterm i)
  have hsub : (quadAtom p q).totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le hsum ?_)
    refine (totalDegree_sq_le _).trans ?_
    have := hX (posEps p q)
    omega
  simp only [atomDegD]
  omega

end Work.WilE4.CAD
