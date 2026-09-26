import Mathlib
import Submission.Work.Smooth.JordanSeparation.GridWalkDefs
import Submission.Work.Smooth.JordanSeparation.plWalk
import Submission.Work.Smooth.JordanSeparation.plApprox
import Submission.Work.Smooth.JordanSeparation.plSplit

/-!
# Generic path algebra for the lattice approximation

* `Path.cast_trans` — a cast of a product of paths is the product of the casts;
* `freeHomotopic_of_conj` — a loop conjugate to `q` is freely homotopic to `q`;
* `joinNat_congr_lt` — a bounded version of `joinNat_congr`;
* `joinNat_blockwise` — the join of `12 * N` pieces is the join of its blocks of twelve;
* `joinNat_conj` — the telescoping of the three-piece paths `e k · s k · (e (k+1))⁻¹`.
-/

namespace Work.SphereJordan

open Set
open Work.Smooth.JordanSeparation

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- A cast of a product of paths is the product of the casts. -/
theorem cast_trans {x y z x' z' : X} (p : Path x y) (q : Path y z) (hx : x' = x) (hz : z' = z) :
    Path.cast (p.trans q) hx hz = (Path.cast p hx rfl).trans (Path.cast q rfl hz) := by
  ext t
  rw [Path.cast_coe, Path.trans_apply, Path.trans_apply, Path.cast_coe, Path.cast_coe]

/-- **A loop conjugate to `q` is freely homotopic to `q`.** -/
theorem freeHomotopic_of_conj {x y : X} (p : Path x x) (q : Path y y) {a : Path x y}
    (h : Path.Homotopic p (a.trans (q.trans a.symm))) : FreeHomotopic p q := by
  refine ⟨a, ?_⟩
  have h1 : Path.Homotopic (a.symm.trans (p.trans a))
      (a.symm.trans ((a.trans (q.trans a.symm)).trans a)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _)
      (Path.Homotopic.hcomp h (Path.Homotopic.refl _))
  have h2 : Path.Homotopic (a.symm.trans ((a.trans (q.trans a.symm)).trans a))
      (a.symm.trans (a.trans ((q.trans a.symm).trans a))) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _)
      (Path.Homotopic.trans_assoc a (q.trans a.symm) a)
  have h3 : Path.Homotopic (a.symm.trans (a.trans ((q.trans a.symm).trans a)))
      (a.symm.trans (a.trans (q.trans (a.symm.trans a)))) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) (Path.Homotopic.hcomp (Path.Homotopic.refl _)
      (Path.Homotopic.trans_assoc q a.symm a))
  have h4 : Path.Homotopic (a.symm.trans (a.trans (q.trans (a.symm.trans a))))
      (a.symm.trans (a.trans (q.trans (Path.refl y)))) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) (Path.Homotopic.hcomp (Path.Homotopic.refl _)
      (Path.Homotopic.hcomp (Path.Homotopic.refl _) (Path.Homotopic.symm_trans a)))
  have h5 : Path.Homotopic (a.symm.trans (a.trans (q.trans (Path.refl y))))
      (a.symm.trans (a.trans q)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) (Path.Homotopic.hcomp (Path.Homotopic.refl _)
      (Path.Homotopic.trans_refl q))
  have h6 : Path.Homotopic (a.symm.trans (a.trans q)) ((a.symm.trans a).trans q) :=
    (Path.Homotopic.trans_assoc a.symm a q).symm
  have h7 : Path.Homotopic ((a.symm.trans a).trans q) ((Path.refl y).trans q) :=
    Path.Homotopic.hcomp (Path.Homotopic.symm_trans a) (Path.Homotopic.refl _)
  have h8 : Path.Homotopic ((Path.refl y).trans q) q := Path.Homotopic.refl_trans q
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8))))))

/-- The recursive join of the restrictions of a path is the `joinNat` of the same family. -/
theorem joinRestr_eq_joinNat {a b : X} (γ : Path a b) (t : ℕ → unitInterval) (j : ℕ) :
    joinRestr γ t j = joinNat (p := fun i => γ (t i)) (fun k => γ.restr (t k) (t (k + 1))) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show joinRestr γ t (j + 1)
        = (joinRestr γ t j).trans (γ.restr (t j) (t (j + 1))) from rfl,
      show joinNat (p := fun i => γ (t i)) (fun k => γ.restr (t k) (t (k + 1))) (j + 1)
        = (joinNat (p := fun i => γ (t i)) (fun k => γ.restr (t k) (t (k + 1))) j).trans
          (γ.restr (t j) (t (j + 1))) from rfl, ih]

/-- A bounded version of `joinNat_congr`: only the first `j` members of the families are
compared. -/
theorem joinNat_congr_lt {p : ℕ → X} {F G : ∀ k, Path (p k) (p (k + 1))} (j : ℕ)
    (h : ∀ k, k < j → Path.Homotopic (F k) (G k)) :
    Path.Homotopic (joinNat F j) (joinNat G j) := by
  induction j with
  | zero => exact Path.Homotopic.refl _
  | succ j ih =>
    rw [show joinNat F (j + 1) = (joinNat F j).trans (F j) from rfl,
        show joinNat G (j + 1) = (joinNat G j).trans (G j) from rfl]
    exact Path.Homotopic.hcomp (ih (fun k hk => h k (Nat.lt_succ_of_lt hk)))
      (h j (Nat.lt_succ_self j))

/-- **The join of `12 * N` paths is the join of its blocks of twelve.** -/
theorem joinNat_blockwise {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) (N : ℕ) :
    Path.Homotopic (joinNat F (12 * N))
      (joinNat (p := fun k => p (12 * k))
        (fun k => joinNat (p := fun j => p (12 * k + j)) (fun j => F (12 * k + j)) 12) N) := by
  induction N with
  | zero => exact Path.Homotopic.refl _
  | succ n ih =>
    refine (joinNat_add F (12 * n) 12).trans ?_
    rw [show joinNat (p := fun k => p (12 * k))
        (fun k => joinNat (p := fun j => p (12 * k + j)) (fun j => F (12 * k + j)) 12) (n + 1)
        = (joinNat (p := fun k => p (12 * k))
            (fun k => joinNat (p := fun j => p (12 * k + j)) (fun j => F (12 * k + j)) 12) n).trans
          (joinNat (p := fun j => p (12 * n + j)) (fun j => F (12 * n + j)) 12) from rfl]
    exact Path.Homotopic.hcomp ih (Path.Homotopic.refl _)

/-- **Cancelling a backtrack inside a product of paths.** -/
theorem trans_conj_cancel {a b c d e f : X} (A : Path a b) (B : Path b c) (E : Path d c)
    (S : Path c e) (EN : Path e f) :
    Path.Homotopic ((A.trans (B.trans E.symm)).trans (E.trans (S.trans EN)))
      ((A.trans (B.trans S)).trans EN) := by
  have h1 : Path.Homotopic ((A.trans (B.trans E.symm)).trans (E.trans (S.trans EN)))
      ((A.trans (B.trans E.symm)).trans ((E.trans S).trans EN)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _)
      (Path.Homotopic.trans_assoc E S EN).symm
  have h2 : Path.Homotopic ((A.trans (B.trans E.symm)).trans ((E.trans S).trans EN))
      (((A.trans (B.trans E.symm)).trans (E.trans S)).trans EN) :=
    (Path.Homotopic.trans_assoc _ _ _).symm
  have h3 : Path.Homotopic (((A.trans (B.trans E.symm)).trans (E.trans S)).trans EN)
      ((A.trans ((B.trans E.symm).trans (E.trans S))).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.trans_assoc A (B.trans E.symm) (E.trans S))
      (Path.Homotopic.refl _)
  have h4 : Path.Homotopic ((A.trans ((B.trans E.symm).trans (E.trans S))).trans EN)
      ((A.trans (B.trans (E.symm.trans (E.trans S)))).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl A)
      (Path.Homotopic.trans_assoc B E.symm (E.trans S))) (Path.Homotopic.refl _)
  have h5 : Path.Homotopic ((A.trans (B.trans (E.symm.trans (E.trans S)))).trans EN)
      ((A.trans (B.trans ((E.symm.trans E).trans S))).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl A)
      (Path.Homotopic.hcomp (Path.Homotopic.refl B)
        (Path.Homotopic.trans_assoc E.symm E S).symm)) (Path.Homotopic.refl _)
  have h6 : Path.Homotopic ((A.trans (B.trans ((E.symm.trans E).trans S))).trans EN)
      ((A.trans (B.trans ((Path.refl c).trans S))).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl A)
      (Path.Homotopic.hcomp (Path.Homotopic.refl B)
        (Path.Homotopic.hcomp (Path.Homotopic.symm_trans E) (Path.Homotopic.refl S))))
      (Path.Homotopic.refl _)
  have h7 : Path.Homotopic ((A.trans (B.trans ((Path.refl c).trans S))).trans EN)
      ((A.trans (B.trans S)).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl A)
      (Path.Homotopic.hcomp (Path.Homotopic.refl B) (Path.Homotopic.refl_trans S)))
      (Path.Homotopic.refl _)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

/-- **The telescoping of the three-piece paths.**  The join of `e k · s k · (e (k+1))⁻¹`,
`k = 0, …, N-1`, is homotopic (relative to its endpoints) to `e 0 · (s 0 · … · s (N-1)) · (e N)⁻¹`. -/
theorem joinNat_conj {y w : ℕ → X} (e : ∀ k, Path (y k) (w k)) (s : ∀ k, Path (w k) (w (k + 1)))
    (N : ℕ) :
    Path.Homotopic (joinNat (fun k => (e k).trans ((s k).trans ((e (k + 1)).symm))) N)
      ((e 0).trans ((joinNat s N).trans ((e N).symm))) := by
  induction N with
  | zero =>
    exact ((Path.Homotopic.hcomp (Path.Homotopic.refl (e 0))
      (Path.Homotopic.refl_trans ((e 0).symm))).trans
        (Path.Homotopic.trans_symm (e 0))).symm
  | succ N ih =>
    rw [show joinNat (fun k => (e k).trans ((s k).trans ((e (k + 1)).symm))) (N + 1) =
        (joinNat (fun k => (e k).trans ((s k).trans ((e (k + 1)).symm))) N).trans
          ((e N).trans ((s N).trans ((e (N + 1)).symm))) from rfl]
    rw [show joinNat s (N + 1) = (joinNat s N).trans (s N) from rfl]
    exact ((Path.Homotopic.hcomp ih (Path.Homotopic.refl _)).trans
      (trans_conj_cancel (e 0) (joinNat s N) (e N) (s N) ((e (N + 1)).symm))).trans
      (Path.Homotopic.trans_assoc (e 0) ((joinNat s N).trans (s N)) ((e (N + 1)).symm))

/-- **Basepoint change for a conjugated loop.**  If `p ≈ a·(m·Z)`, `Z ≈ Xp·a⁻¹` and
`m·Xp ≈ q`, then `p ≈ a·(q·a⁻¹)`. -/
theorem homotopic_conj_glue {x y u : X}
    (p : Path x x) (q : Path y y) (a : Path x y) (m : Path y u) (Z : Path u x) (Xp : Path u y)
    (h1 : Path.Homotopic p (a.trans (m.trans Z)))
    (h2 : Path.Homotopic Z (Xp.trans a.symm))
    (h3 : Path.Homotopic (m.trans Xp) q) :
    Path.Homotopic p (a.trans (q.trans a.symm)) := by
  have h2' : Path.Homotopic (m.trans Z) (m.trans (Xp.trans a.symm)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl m) h2
  have h2'' : Path.Homotopic (m.trans Z) ((m.trans Xp).trans a.symm) :=
    h2'.trans (Path.Homotopic.trans_assoc m Xp a.symm).symm
  have h4 : Path.Homotopic (a.trans (m.trans Z)) (a.trans ((m.trans Xp).trans a.symm)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl a) h2''
  have h5 : Path.Homotopic (a.trans ((m.trans Xp).trans a.symm)) (a.trans (q.trans a.symm)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl a)
      (Path.Homotopic.hcomp h3 (Path.Homotopic.refl a.symm))
  exact h1.trans (h4.trans h5)

end

end Work.SphereJordan
