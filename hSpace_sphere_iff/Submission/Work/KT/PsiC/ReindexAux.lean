import Mathlib
import Submission.Work.KT.PsiC.Setup
import Submission.Work.KT.PsiC.Frame
import Submission.Work.KT.Psi.cls_conj
import Submission.Work.KT.Psi.cls_split
import Submission.Work.KT.Psi.cls_orbit
import Submission.Work.KT.Psi.OrbitBasic

/-!
# `Work.KT.PsiC.ReindexAux` — `clsM` transport of the class lemmas of `Work.KT.Psi`
-/

namespace Work.KT.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-! ## Reindexing of the ring operations -/

theorem reindex_zero' {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    Matrix.reindex e e (0 : Matrix ι ι A) = 0 := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.zero_apply]

theorem reindex_neg' {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (X : Matrix ι ι A) :
    Matrix.reindex e e (-X) = -Matrix.reindex e e X := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply]

theorem reindex_sub' {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (X Y : Matrix ι ι A) :
    Matrix.reindex e e (X - Y) = Matrix.reindex e e X - Matrix.reindex e e Y := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]

theorem reindex_csmul' {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (c : ℂ)
    (X : Matrix ι ι A) :
    Matrix.reindex e e (c • X) = c • Matrix.reindex e e X := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]

theorem reindex_pow' {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (X : Matrix ι ι A) (n : ℕ) :
    Matrix.reindex e e (X ^ n) = Matrix.reindex e e X ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, reindex_one']
  | succ n ih => rw [pow_succ, reindex_mul', ih, pow_succ]

theorem reindex_sum_range' {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (m : ℕ)
    (f : ℕ → Matrix ι ι A) :
    Matrix.reindex e e (∑ i ∈ Finset.range m, f i) =
      ∑ i ∈ Finset.range m, Matrix.reindex e e (f i) := by
  induction m with
  | zero => simp [reindex_zero']
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, reindex_add', ih]

theorem reindex_sum_smul_range' {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (m : ℕ)
    (c : ℕ → ℂ) (X : ℕ → Matrix ι ι A) :
    Matrix.reindex e e (∑ i ∈ Finset.range m, c i • X i) =
      ∑ i ∈ Finset.range m, c i • Matrix.reindex e e (X i) := by
  induction m with
  | zero => simp [reindex_zero']
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, reindex_add', reindex_csmul', ih]

/-! ## A Murray–von Neumann class lemma for arbitrary index types -/

theorem clsM_eq_of_mvN {ι : Type} [Fintype ι] [DecidableEq ι] {R G : Matrix ι ι A}
    (hR : R * R = R) (hG : G * G = G) (a b : Matrix ι ι A) (h1 : b * a = R)
    (h2 : a * b = G) : clsM ι R = clsM ι G := by
  have hR' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) R *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) R =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) R := by
    rw [← reindex_mul' (Fintype.equivFin ι) R R, hR]
  have hG' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) G *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) G =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) G := by
    rw [← reindex_mul' (Fintype.equivFin ι) G G, hG]
  have h1' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) b *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) a =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) R := by
    rw [← reindex_mul' (Fintype.equivFin ι) b a, h1]
  have h2' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) a *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) b =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) G := by
    rw [← reindex_mul' (Fintype.equivFin ι) a b, h2]
  rw [show clsM ι R = cls ⟨Fintype.card ι, Matrix.reindex (Fintype.equivFin ι)
      (Fintype.equivFin ι) R⟩ from rfl,
    show clsM ι G = cls ⟨Fintype.card ι, Matrix.reindex (Fintype.equivFin ι)
      (Fintype.equivFin ι) G⟩ from rfl]
  refine cls_of_mvN (p := (⟨Fintype.card ι,
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) R⟩ : Mat A))
    (q := (⟨Fintype.card ι,
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) G⟩ : Mat A)) hR' hG' ?_
  refine ⟨Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) a,
    Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) b, ?_, ?_⟩
  · show Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) b *
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) a =
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) R
    exact h1'
  · show Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) a *
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) b =
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) G
    exact h2'

/-! ## `clsM` versions of the class lemmas -/

/-- `clsM` is invariant under reindexing (for idempotent matrices). -/
theorem clsM_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι ι A)
    (hM : M * M = M) (e : ι ≃ κ) :
    clsM ι M = clsM κ (Matrix.reindex e e M) := by
  have hMr : Matrix.reindex e e M * Matrix.reindex e e M = Matrix.reindex e e M := by
    rw [← reindex_mul' e M M, hM]
  calc clsM ι M = clsE M (Fintype.card ι) (Fintype.equivFin ι) := rfl
    _ = clsE M (Fintype.card κ) (e.trans (Fintype.equivFin κ)) :=
          (clsE_wellDefined hM (e.trans (Fintype.equivFin κ)) (Fintype.equivFin ι)).symm
    _ = clsE (Matrix.reindex e e M) (Fintype.card κ)
          (e.symm.trans (e.trans (Fintype.equivFin κ))) :=
          (clsE_reindex M (Fintype.card κ) (e.trans (Fintype.equivFin κ)) e).symm
    _ = clsE (Matrix.reindex e e M) (Fintype.card κ) (Fintype.equivFin κ) :=
          (clsE_wellDefined hMr (Fintype.equivFin κ)
            (e.symm.trans (e.trans (Fintype.equivFin κ)))).symm
    _ = clsM κ (Matrix.reindex e e M) := rfl

/-- Splitting a projection by a commuting projection (`clsM` form). -/
theorem clsM_split {ι : Type} [Fintype ι] [DecidableEq ι] (P E : Matrix ι ι A)
    (hP : P * P = P) (hE : E * E = E) (hPE : P * E = E * P) :
    clsM ι P = clsM ι (P * E) + clsM ι (P * (1 - E)) := by
  have hP' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) P *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) P =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) P := by
    rw [← reindex_mul' (Fintype.equivFin ι) P P, hP]
  have hE' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) E *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) E =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) E := by
    rw [← reindex_mul' (Fintype.equivFin ι) E E, hE]
  have hPE' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) P *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) E =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) E *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) P := by
    rw [← reindex_mul' (Fintype.equivFin ι) P E, ← reindex_mul' (Fintype.equivFin ι) E P, hPE]
  have h1 := cls_split A (Fintype.card ι)
    (Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) P)
    (Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) E) hP' hE' hPE'
  simp only [clsM_eq_cls]
  rw [reindex_mul', reindex_mul', reindex_sub', reindex_one']
  exact h1

/-- Conjugation invariance of `clsM`. -/
theorem clsM_conj {ι : Type} [Fintype ι] [DecidableEq ι] (P u v : Matrix ι ι A)
    (huv : u * v = 1) (hvu : v * u = 1) :
    clsM ι (u * P * v) = clsM ι P := by
  have huv' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) u *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) v = 1 := by
    rw [← reindex_mul' (Fintype.equivFin ι) u v, huv, reindex_one']
  have hvu' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) v *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) u = 1 := by
    rw [← reindex_mul' (Fintype.equivFin ι) v u, hvu, reindex_one']
  have h2 : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (u * P * v) =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) u *
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) P *
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) v := by
    rw [reindex_mul', reindex_mul']
  have h1 := cls_conj A (Fintype.card ι)
    (Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) P)
    (Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) u)
    (Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) v) huv' hvu'
  simp only [clsM_eq_cls]
  rw [h2]
  exact h1

/-- **Free-orbit result, `clsM` form.** -/
theorem clsM_orbit {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) (hk : 0 < k)
    (P F g : Matrix ι ι A) (hP : P * P = P) (hF : F * F = F) (hg : g ^ k = 1)
    (hPg : P * g = g * P) (hPF : P * F = F * P)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0)
    (lam : ℂ) (hlam : lam ^ k = 1) :
    clsM ι (P * (orbSum g F k * orbitSpec lam g k)) = clsM ι (P * F) := by
  obtain ⟨hRidem, hGidem, hGRG, hRGR⟩ :=
    cls_orbit_core (M := Matrix ι ι A) k hk P F g hP hF hg hPg hPF horth lam hlam
  have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  refine clsM_eq_of_mvN hRidem hGidem
    ((k : ℂ) • ((P * F) * (P * (orbSum g F k * orbitSpec lam g k))))
    ((P * (orbSum g F k * orbitSpec lam g k)) * (P * F)) ?_ ?_
  · rw [mul_smul_comm]
    have hrr : ((P * (orbSum g F k * orbitSpec lam g k)) * (P * F)) *
        ((P * F) * (P * (orbSum g F k * orbitSpec lam g k))) =
        (P * (orbSum g F k * orbitSpec lam g k)) * (P * F) *
          (P * (orbSum g F k * orbitSpec lam g k)) := by
      rw [← mul_assoc, mul_assoc (P * (orbSum g F k * orbitSpec lam g k)) (P * F) (P * F),
        hGidem]
    rw [hrr, hRGR, ← Algebra.smul_def ((k : ℂ)⁻¹) (P * (orbSum g F k * orbitSpec lam g k)),
      smul_smul, mul_inv_cancel₀ hkne, one_smul]
  · rw [smul_mul_assoc]
    have hrr : ((P * F) * (P * (orbSum g F k * orbitSpec lam g k))) *
        ((P * (orbSum g F k * orbitSpec lam g k)) * (P * F)) =
        (P * F) * (P * (orbSum g F k * orbitSpec lam g k)) * (P * F) := by
      rw [← mul_assoc, mul_assoc (P * F) (P * (orbSum g F k * orbitSpec lam g k))
        (P * (orbSum g F k * orbitSpec lam g k)), hRidem]
    rw [hrr, hGRG, ← Algebra.smul_def ((k : ℂ)⁻¹) (P * F), smul_smul, mul_inv_cancel₀ hkne,
      one_smul]

end

end Work.KT.PsiC
