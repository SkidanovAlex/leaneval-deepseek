/-
  WilE9G — **the kernel of the G4 construction**: the target lemma of this file builds the
  Lagrange stratum of `Work.WilE9G.Lagrange.lagStratum` and checks that it contains every
  Lagrange point at which `lagJac` is invertible.

  The mathematical content is that the fibre block of the constructed stratum at a Lagrange point
  is the *true* Jacobian of the Lagrange system (`lagJacTrue`), and that `lagJacTrue` and `lagJac`
  have the same determinant whenever the Lagrange equations and the normalisation hold: the two
  matrices differ only in the `(L, yt)` block, which is transposed — this is handled by the
  delegated `lagJacTrue_det`.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.Defs
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Jac
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE9G.Lagrange.eaD_pad
import Submission.Work.WilE9G.Lagrange.lagPoint_apply
import Submission.Work.WilE9G.Lagrange.lagEqs_eval
import Submission.Work.WilE9G.Lagrange.lagBlock_lagPoint
import Submission.Work.WilE9G.Lagrange.lagJacTrue_det
import Submission.Work.WilE9G.Lagrange.lagStratum_good
import Submission.Work.WilE9G.Lagrange.lagStratum_deg

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp Work.WilE9G

/-! ## Elementary helper lemmas -/

/-- `eaEval` commutes with the determinant of a matrix of EA-polynomials. -/
theorem eaEval_det_eval {N r q : ℕ} (c : EAChain N r)
    (A : Matrix (Fin q) (Fin q) (EAPoly N r)) (w : Fin N → ℝ) :
    eaEval c A.det w = (A.map (fun P => eaEval c P w)).det := by
  have h := RingHom.map_det
    (MvPolynomial.eval₂Hom (RingHom.id ℝ) (Sum.elim w (fun j => Real.exp (c.ell j w)))) A
  have h2 : (MvPolynomial.eval₂Hom (RingHom.id ℝ)
      (Sum.elim w (fun j => Real.exp (c.ell j w)))).mapMatrix A
      = A.map (fun P => eaEval c P w) := by
    ext i j; rfl
  rw [h2] at h
  exact h

/-- The equation of the constructed stratum, written in the block form of `lagJac`. -/
theorem lagEqs_apply {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) :
    lagEqs S Phi c a
      = Fin.addCases (fun l : Fin (1 + m) => lagL S Phi c l)
          (fun s : Fin (S.j + 1) =>
            Fin.addCases (fun b : Fin S.j => lagH S b) (fun _ : Fin 1 => lagN S) s)
          (lagEquiv m S.j a) := rfl

/-- At an `L`-index, the equation of the constructed stratum is the corresponding Lagrange
equation. -/
theorem lagEqs_apply_of_lt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) (ha : a.val < 1 + m) :
    lagEqs S Phi c a = lagL S Phi c ⟨a.val, ha⟩ := by
  rw [lagEqs_apply]
  have h : lagEquiv m S.j a = Fin.castAdd (S.j + 1) (⟨a.val, ha⟩ : Fin (1 + m)) := by
    apply Fin.ext
    simp
  rw [h, Fin.addCases_left]

/-- At an index of the middle block, the equation of the constructed stratum is the corresponding
equation of `S`. -/
theorem lagEqs_apply_of_mid {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) (ha : 1 + m ≤ a.val) (ha2 : a.val < 1 + m + S.j) :
    lagEqs S Phi c a = lagH S ⟨a.val - (1 + m), by omega⟩ := by
  rw [lagEqs_apply]
  have h : lagEquiv m S.j a
      = Fin.natAdd (1 + m)
          (Fin.castAdd 1 (⟨a.val - (1 + m), by omega⟩ : Fin S.j)) := by
    apply Fin.ext
    simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_castAdd]
    omega
  rw [h, Fin.addCases_right, Fin.addCases_left]

/-- At the last index, the equation of the constructed stratum is the normalisation. -/
theorem lagEqs_apply_of_last {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) (ha : a.val = 1 + m + S.j) :
    lagEqs S Phi c a = lagN S := by
  rw [lagEqs_apply]
  have h : lagEquiv m S.j a = Fin.natAdd (1 + m) (Fin.last S.j) := by
    apply Fin.ext
    simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_last]
    omega
  rw [h, Fin.addCases_right]
  rw [show (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1) from Fin.ext (by simp),
    Fin.addCases_right]

/-- The base-and-fibre coordinates of a point of the Lagrange stratum. -/
theorem lagPoint_apply_castLE {n m j : ℕ} (hk : n + (1 + m) ≤ n + (1 + (m + j + 1)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ) (i : Fin (n + (1 + m))) :
    lagPoint z mu mu0 (Fin.castLE hk i) = z i :=
  (lagPoint_apply hk z mu mu0).2.1 i

/-- The value of the `i`-th interior condition of `lagPos` at a point. -/
theorem eaEval_one_sub_sq {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (w : Fin (n + (1 + (m + S.j + 1))) → ℝ) (hk : n + (1 + m) ≤ n + (1 + (m + S.j + 1)))
    (i : Fin (n + (1 + m))) :
    eaEval (lagChain S) (1 - (MvPolynomial.X (Sum.inl (Fin.castLE hk i))) ^ 2) w
      = 1 - (w (Fin.castLE hk i)) ^ 2 := by
  simp only [eaEval, map_sub, map_one, map_pow, MvPolynomial.eval_X, Sum.elim_inl]

/-- The multipliers of a normalised Lagrange point lie in the unit interval. -/
theorem abs_mu_le_one {j : ℕ} {mu : Fin j → ℝ} {mu0 : ℝ} (h : LagNorm mu mu0) (a : Fin j) :
    |mu a| ≤ 1 := by
  have h1 : (∑ b, (mu b) ^ 2) + mu0 ^ 2 = 1 := h
  have h2 : (mu a) ^ 2 ≤ (∑ b, (mu b) ^ 2) :=
    Finset.single_le_sum (f := fun b : Fin j => (mu b) ^ 2) (fun b _ => sq_nonneg _)
      (Finset.mem_univ a)
  have h3 : (0 : ℝ) ≤ mu0 ^ 2 := sq_nonneg _
  have h4 : (mu a) ^ 2 ≤ 1 := by linarith
  exact (sq_le_one_iff_abs_le_one (mu a)).mp h4

/-- The normalising multiplier of a Lagrange point lies in the unit interval. -/
theorem abs_mu0_le_one {j : ℕ} {mu : Fin j → ℝ} {mu0 : ℝ} (h : LagNorm mu mu0) :
    |mu0| ≤ 1 := by
  have h1 : (∑ b, (mu b) ^ 2) + mu0 ^ 2 = 1 := h
  have h3 : (0 : ℝ) ≤ ∑ b, (mu b) ^ 2 := Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have h4 : mu0 ^ 2 ≤ 1 := by linarith
  exact (sq_le_one_iff_abs_le_one mu0).mp h4

/-- A point of the Lagrange stratum lies in the cube. -/
theorem lagPoint_mem_cubeC {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (hlt : ∀ i : Fin (n + (1 + m)), |z i| < 1) (hNorm : LagNorm mu mu0) :
    lagPoint z mu mu0 ∈ cubeC (n + (1 + (m + S.j + 1))) := by
  intro i
  obtain ⟨htake, hcast, hmu, hmu0⟩ :=
    lagPoint_apply (n := n) (m := m) (j := S.j) (by omega) z mu mu0
  rcases lt_or_ge i.val (n + (1 + m)) with h | h
  · have he : Fin.castLE (by omega : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) ⟨i.val, h⟩ = i :=
      Fin.ext rfl
    rw [← he, hcast ⟨i.val, h⟩]
    exact le_of_lt (hlt ⟨i.val, h⟩)
  · have hd : i.val - (n + (1 + m)) < S.j + 1 := by
      have hi : i.val < n + (1 + m) + (S.j + 1) := by
        have := i.isLt
        omega
      omega
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hlt' | heq
    · -- a multiplier coordinate `μ a`
      have he : muIdx n m (⟨i.val - (n + (1 + m)), hlt'⟩ : Fin S.j) = i := by
        apply Fin.ext
        simp only [muIdx_val]
        omega
      rw [← he, hmu ⟨i.val - (n + (1 + m)), hlt'⟩]
      exact abs_mu_le_one hNorm _
    · -- the normalising multiplier `μ₀`
      have he : mu0Idx n m S.j = i := by
        apply Fin.ext
        simp only [mu0Idx_val]
        omega
      rw [← he, hmu0]
      exact abs_mu0_le_one hNorm

/-- At a Lagrange point the determinant of the fibre block of the constructed stratum is
nonvanishing: it is the determinant of the *true* Jacobian of the Lagrange system, which agrees
with `det (lagJac …)` there. -/
theorem lagDet_eval_ne_zero {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (hEq : LagEq S Phi c z mu mu0) (hNorm : LagNorm mu mu0)
    (hdet : (lagJac S Phi c z mu mu0).det ≠ 0) :
    eaEval (lagChain S) (lagDet S Phi c) (lagPoint z mu mu0) ≠ 0 := by
  have h1 : eaEval (lagChain S) (lagDet S Phi c) (lagPoint z mu mu0)
      = (lagBlock S Phi c (lagPoint z mu mu0)).det := by
    rw [lagDet, eaEval_det_eval]
    congr 1
  have h2 : (lagBlock S Phi c (lagPoint z mu mu0)).det ≠ 0 := by
    simpa [lagBlock_lagPoint S Phi c z mu mu0,
      Matrix.det_submatrix_equiv_self (lagEquiv m S.j) (lagJacTrue S Phi c z mu mu0),
      lagJacTrue_det S Phi c z mu mu0 hEq hNorm] using hdet
  rw [h1]
  exact h2

theorem exists_lagrange_stratum {n m : ℕ} (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (S : Work.WilE9G.AmbStratum (n + (1 + m))),
      S.j ≤ n + (1 + m) → S.X.fmt ≤ F → S.Good →
      ∀ (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ),
        (∀ z ∈ S.X.set, 0 < WilkiesDesign.E.eaEval S.X.c Phi z) →
        ∃ E : Work.WilE9.Sharp.EffStratum n (m + S.j + 1),
          E.Good ∧ E.X.basics.length ≤ 2 ∧ E.X.fmt ≤ a ∧
          E.X.deg ≤ b.eval (S.deg + WilkiesDesign.E.atomDeg Phi) ∧
          (∀ (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ),
            z ∈ S.X.set → (∀ i : Fin (n + (1 + m)), |z i| < 1) →
            Work.WilE9G.LagEq S Phi c z mu mu0 → Work.WilE9G.LagNorm mu mu0 →
            (Work.WilE9G.lagJac S Phi c z mu mu0).det ≠ 0 →
            Work.WilE9G.lagPoint z mu mu0 ∈ E.X.set) := by
  refine ⟨2 * F + 1,
    Polynomial.C ((3 * F + 2) * (4 * F + 5)) * Polynomial.X
      + Polynomial.C (4 * ((3 * F + 2) * (4 * F + 5))), ?_⟩
  intro S hj hfmt hGood Phi c _hpos
  have hbk : (Polynomial.C ((3 * F + 2) * (4 * F + 5)) * Polynomial.X
      + Polynomial.C (4 * ((3 * F + 2) * (4 * F + 5)))).eval
        (S.deg + atomDeg Phi)
      = ((3 * F + 2) * (4 * F + 5)) * (S.deg + atomDeg Phi + 4) := by
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  refine ⟨lagStratum S Phi c, lagStratum_good S Phi c, ?hlen, ?hfmt, ?hdeg, ?hmem⟩
  · show (lagStratum S Phi c).X.basics.length ≤ 2
    simp [lagStratum]
  · have h1 : (lagStratum S Phi c).X.fmt = (n + (1 + m)) + S.j + 1 + S.X.r := by
      show n + (1 + (m + S.j + 1)) + S.X.r = (n + (1 + m)) + S.j + 1 + S.X.r
      omega
    have h2 : S.X.fmt = (n + (1 + m)) + S.X.r := rfl
    rw [h1]
    omega
  · rw [hbk]
    exact lagStratum_deg S Phi c F hj hfmt
  · intro z mu mu0 hz hlt hEq hNorm hdet
    set w : Fin (n + (1 + (m + S.j + 1))) → ℝ := lagPoint z mu mu0 with hw
    have hcube : w ∈ cubeC (n + (1 + (m + S.j + 1))) := lagPoint_mem_cubeC S z mu mu0 hlt hNorm
    obtain ⟨htake, hcast, hmu, hmu0⟩ :=
      lagPoint_apply (n := n) (m := m) (j := S.j) (by omega) z mu mu0
    obtain ⟨hH, hL, hN⟩ := lagEqs_eval S Phi c z mu mu0
    have heqs : ∀ f ∈ List.ofFn (lagEqs S Phi c), eaEval (lagChain S) f w = 0 := by
      intro f hf
      rw [List.mem_ofFn] at hf
      obtain ⟨a, rfl⟩ := hf
      rcases lt_or_ge a.val (1 + m) with ha | ha
      · rw [lagEqs_apply_of_lt S Phi c a ha, hL ⟨a.val, ha⟩, ← hEq ⟨a.val, ha⟩]
        ring
      · by_cases ha2 : a.val < 1 + m + S.j
        · rw [lagEqs_apply_of_mid S Phi c a ha ha2, hH ⟨a.val - (1 + m), by omega⟩,
            AmbStratum_eq_zero S hGood hz ⟨a.val - (1 + m), by omega⟩]
        · have hlast : a.val = 1 + m + S.j := by
            have := a.isLt
            omega
          rw [lagEqs_apply_of_last S Phi c a hlast, hN]
          have hnorm : (∑ a : Fin S.j, (mu a) ^ 2) + mu0 ^ 2 = 1 := hNorm
          linarith
    have hpos : ∀ g ∈ lagPos S Phi c, 0 < eaEval (lagChain S) g w := by
      intro g hg
      rw [lagPos] at hg
      rcases List.mem_cons.mp hg with h | h
      · rw [h]
        have hne : eaEval (lagChain S) (lagDet S Phi c) w ≠ 0 :=
          lagDet_eval_ne_zero S Phi c z mu mu0 hEq hNorm hdet
        have hmul : eaEval (lagChain S) (lagDet S Phi c * lagDet S Phi c) w
            = eaEval (lagChain S) (lagDet S Phi c) w
              * eaEval (lagChain S) (lagDet S Phi c) w := by
          simp only [eaEval, map_mul]
        rw [hmul]
        exact (mul_self_pos).mpr hne
      · rw [List.mem_ofFn] at h
        obtain ⟨i, rfl⟩ := h
        rw [eaEval_one_sub_sq]
        rw [hw, lagPoint_apply_castLE]
        have h1 : -1 < z i := (abs_lt.mp (hlt i)).1
        have h2 : z i < 1 := (abs_lt.mp (hlt i)).2
        nlinarith
    have hmem : w ∈ (lagStratum S Phi c).X.set := by
      refine ⟨hcube, ⟨⟨List.ofFn (lagEqs S Phi c), lagPos S Phi c⟩, ?_, heqs, hpos⟩⟩
      simp only [lagStratum]
      exact List.mem_singleton_self _
    exact hmem

end Work.WilE9G.Lagrange
