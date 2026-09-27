import Mathlib
import Submission.Work.KT.Psi.psi3sum_Setup
import Submission.Work.KT.Psi.clsM_idem_add
import Submission.Work.KT.PsiC.cls_cyclic

/-!
# `Work.KT.Psi.clsM_orb3`

Let `X`, `e` be idempotent matrices over a `ℂ`-algebra `A` indexed by `SQ S = (S × S) × S`,
`u = uPerm A S` the permutation matrix of the cyclic permutation `cyc3 S` (of order three,
`u * u * u = 1`), `X` commuting with `e` and `u`, and `e * u * e = 0`, `e * (u * u) * e = 0`.

Writing `orb3 S e = e + u*e*(u*u) + (u*u)*e*u` for the free orbit sum of `e`, and
`Cp S lam = (1/3)*(1 + λ⁻¹ u + λ⁻² u²)` for the spectral projector of `u` (λ³ = 1), we show

`clsM (SQ S) (X * Cp S lam * orb3 S e) = clsM (SQ S) (X * e)`.

The proof has three ingredients:

* `clsM_orb3_Cp` rewrites `Cp S lam` into the "matrix algebraMap" form used by
  `Work.KT.PsiC.cyclic_core`;
* `clsM_orb3_Qform` shows that the orbit sum `e + u e u² + u² e u` commutes with the
  projector `1 + λ⁻¹ u + λ⁻² u²` (the orbit sum commutes with `u` because `u³ = 1`), which
  lets us commute the two factors in `X * Cp S lam * orb3 S e`;
* `Work.KT.PsiC.cyclic_core` then exhibits the Murray–von Neumann equivalence between
  `X * orb3 S e * Cp S lam` and `X * e`, and `clsM_orb3_mvN` transports it to `clsM`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-! ## Elementary helpers -/

/-- On the matrix ring, `algebraMap ℂ (Matrix ι ι A) c` acts as the `A`-scalar
`algebraMap ℂ A c`. -/
lemma clsM_orb3_algMap_mul {A : Type} [Ring A] [Algebra ℂ A] {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : ℂ) (M : Matrix ι ι A) :
    algebraMap ℂ (Matrix ι ι A) c * M = algebraMap ℂ A c • M := by
  rw [← Algebra.smul_def c M]
  ext i j
  simp only [Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]

/-- Murray–von Neumann equivalent idempotents have the same class in `K₀`, for matrices over an
arbitrary finite index type. -/
lemma clsM_orb3_mvN {A : Type} [Ring A] [Algebra ℂ A] {ι : Type} [Fintype ι]
    {p q : Matrix ι ι A} (hp : p * p = p) (hq : q * q = q)
    (h : ∃ a b : Matrix ι ι A, b * a = p ∧ a * b = q) :
    clsM ι p = clsM ι q := by
  obtain ⟨a, b, hba, hab⟩ := h
  rw [clsM_eq_cls, clsM_eq_cls]
  set τ := Fintype.equivFin ι with hτ
  have hp' : Matrix.reindex τ τ p * Matrix.reindex τ τ p = Matrix.reindex τ τ p := by
    rw [← reindex_mul', hp]
  have hq' : Matrix.reindex τ τ q * Matrix.reindex τ τ q = Matrix.reindex τ τ q := by
    rw [← reindex_mul', hq]
  refine cls_eq_of_MvN hp' hq' ⟨Matrix.reindex τ τ a, Matrix.reindex τ τ b, ?_, ?_⟩
  · show Matrix.reindex τ τ b * Matrix.reindex τ τ a = Matrix.reindex τ τ p
    rw [← reindex_mul', hba]
  · show Matrix.reindex τ τ a * Matrix.reindex τ τ b = Matrix.reindex τ τ q
    rw [← reindex_mul', hab]

/-! ## The orbit sum commutes with the cyclic generator and its spectral projectors -/

/-- `e + u e u² + u² e u` commutes with `u` when `u³ = 1`. -/
lemma clsM_orb3_orbSum_comm {M : Type} [Ring M] (e u : M) (hu : u*u*u = 1) :
    u * (e + u*e*(u*u) + (u*u)*e*u) = (e + u*e*(u*u) + (u*u)*e*u) * u := by
  have hu' : u*(u*u) = 1 := by rw [← mul_assoc]; exact hu
  have huu : ∀ x : M, u*(u*(u*x)) = x := by
    intro x; rw [← mul_assoc, ← mul_assoc, hu, one_mul]
  noncomm_ring [hu']
  simp only [huu]

/-- `e + u e u² + u² e u` commutes with `1 + u + u²` when `u³ = 1`. -/
lemma clsM_orb3_QE {M : Type} [Ring M] (e u : M) (hu : u*u*u = 1) :
    (1 + u + u*u) * (e + u*e*(u*u) + (u*u)*e*u)
      = (e + u*e*(u*u) + (u*u)*e*u) * (1 + u + u*u) := by
  have huE : u * (e + u*e*(u*u) + (u*u)*e*u) = (e + u*e*(u*u) + (u*u)*e*u) * u :=
    clsM_orb3_orbSum_comm e u hu
  have hu2E : (u*u) * (e + u*e*(u*u) + (u*u)*e*u)
      = (e + u*e*(u*u) + (u*u)*e*u) * (u*u) := by
    calc (u*u) * (e + u*e*(u*u) + (u*u)*e*u)
        = u * (u * (e + u*e*(u*u) + (u*u)*e*u)) := mul_assoc u u _
      _ = u * ((e + u*e*(u*u) + (u*u)*e*u) * u) := by rw [huE]
      _ = (u * (e + u*e*(u*u) + (u*u)*e*u)) * u := (mul_assoc u _ u).symm
      _ = ((e + u*e*(u*u) + (u*u)*e*u) * u) * u := by rw [huE]
      _ = (e + u*e*(u*u) + (u*u)*e*u) * (u*u) := mul_assoc _ u u
  calc (1 + u + u*u) * (e + u*e*(u*u) + (u*u)*e*u)
      = (e + u*e*(u*u) + (u*u)*e*u) + u * (e + u*e*(u*u) + (u*u)*e*u)
          + (u*u) * (e + u*e*(u*u) + (u*u)*e*u) := by simp only [add_mul, one_mul]
    _ = (e + u*e*(u*u) + (u*u)*e*u) + (e + u*e*(u*u) + (u*u)*e*u) * u
          + (e + u*e*(u*u) + (u*u)*e*u) * (u*u) := by rw [huE, hu2E]
    _ = (e + u*e*(u*u) + (u*u)*e*u) * (1 + u + u*u) := by simp only [mul_add, mul_one]

/-! ## Twisting the projector by a scalar `λ⁻¹` -/

/-- `(algebraMap c * u)² = algebraMap (c²) * u²`. -/
lemma clsM_orb3_usq {R : Type} [Ring R] [Algebra ℂ R] (c : ℂ) (u : R) :
    algebraMap ℂ R (c^2) * (u*u) = (algebraMap ℂ R c * u) * (algebraMap ℂ R c * u) := by
  rw [← Algebra.smul_def c u, ← Algebra.smul_def (c^2) (u*u), smul_mul_smul, ← pow_two c]

/-- `(algebraMap c * u)³ = 1` when `c³ = 1` and `u³ = 1`. -/
lemma clsM_orb3_us3 {R : Type} [Ring R] [Algebra ℂ R] (c : ℂ) (u : R)
    (hc : c^3 = 1) (hu : u*u*u = 1) :
    (algebraMap ℂ R c * u) * (algebraMap ℂ R c * u) * (algebraMap ℂ R c * u) = 1 := by
  have hu3 : u^3 = 1 := by
    rw [show (3:ℕ) = 2+1 from rfl, pow_succ, pow_two]; exact hu
  rw [← Algebra.smul_def c u, smul_mul_smul, smul_mul_smul,
      show (c*c)*c = c^3 by ring,
      show (u*u)*u = u^3 by rw [show (3:ℕ) = 2+1 from rfl, pow_succ, pow_two]]
  rw [hc, one_smul, hu3]

/-- Replacing `u` by `algebraMap c * u` in the orbit sum, when `c³ = 1`. -/
lemma clsM_orb3_E_twist {R : Type} [Ring R] [Algebra ℂ R] (e u : R) (c : ℂ) (hc : c^3 = 1) :
    e + (algebraMap ℂ R c * u)*e*((algebraMap ℂ R c * u)*(algebraMap ℂ R c * u))
      + ((algebraMap ℂ R c * u)*(algebraMap ℂ R c * u))*e*(algebraMap ℂ R c * u)
    = e + u*e*(u*u) + (u*u)*e*u := by
  have h1 : (algebraMap ℂ R c * u)*e*((algebraMap ℂ R c * u)*(algebraMap ℂ R c * u))
      = u*e*(u*u) := by
    rw [← clsM_orb3_usq c u, ← Algebra.smul_def c u, ← Algebra.smul_def (c^2) (u*u),
        smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
        show c * c^2 = 1 by rw [show c*c^2 = c^3 by ring, hc], one_smul]
  have h2 : ((algebraMap ℂ R c * u)*(algebraMap ℂ R c * u))*e*(algebraMap ℂ R c * u)
      = (u*u)*e*u := by
    rw [← clsM_orb3_usq c u, ← Algebra.smul_def c u, ← Algebra.smul_def (c^2) (u*u),
        smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
        show c^2 * c = 1 by rw [show c^2*c = c^3 by ring, hc], one_smul]
  rw [h1, h2]

/-- `1 + λ⁻¹ u + λ⁻² u²` commutes with `e + u e u² + u² e u`; the scalar `c` plays the role of
`λ⁻¹`. -/
lemma clsM_orb3_Qform {R : Type} [Ring R] [Algebra ℂ R] (e u : R) (c : ℂ)
    (hc : c^3 = 1) (hu : u*u*u = 1) :
    (1 + algebraMap ℂ R c * u + algebraMap ℂ R (c^2) * (u*u)) * (e + u*e*(u*u) + (u*u)*e*u)
      = (e + u*e*(u*u) + (u*u)*e*u)
        * (1 + algebraMap ℂ R c * u + algebraMap ℂ R (c^2) * (u*u)) := by
  rw [clsM_orb3_usq c u, ← clsM_orb3_E_twist (R := R) e u c hc]
  exact clsM_orb3_QE e (algebraMap ℂ R c * u) (clsM_orb3_us3 c u hc hu)

/-! ## The main lemma -/

/-- The spectral projector `Cp S lam` in the "matrix algebraMap" form. -/
lemma clsM_orb3_Cp {A : Type} [Ring A] [Algebra ℂ A] {S : Type} [Fintype S] [DecidableEq S]
    (lam : ℂ) :
    Cp S lam = algebraMap ℂ (Matrix (SQ S) (SQ S) A) (1/3) *
      (1 + algebraMap ℂ (Matrix (SQ S) (SQ S) A) lam⁻¹ * uPerm A S +
        algebraMap ℂ (Matrix (SQ S) (SQ S) A) (lam⁻¹ ^ 2) * (uPerm A S * uPerm A S)) := by
  unfold Cp uPerm
  simp only [clsM_orb3_algMap_mul]


theorem clsM_orb3 {A : Type} [Ring A] [Algebra ℂ A] {S : Type} [Fintype S] [DecidableEq S]
    (X e : Matrix (Work.KT.Psi.SQ S) (Work.KT.Psi.SQ S) A)
    (hX : X * X = X) (he : e * e = e)
    (hu : Work.KT.Psi.uPerm A S * Work.KT.Psi.uPerm A S * Work.KT.Psi.uPerm A S = 1)
    (hXe : X * e = e * X) (hXu : X * Work.KT.Psi.uPerm A S = Work.KT.Psi.uPerm A S * X)
    (heu : e * Work.KT.Psi.uPerm A S * e = 0)
    (heu2 : e * (Work.KT.Psi.uPerm A S * Work.KT.Psi.uPerm A S) * e = 0)
    (lam : ℂ) (hlam : lam ^ 3 = 1) :
    Work.KT.Psi.clsM (Work.KT.Psi.SQ S) (X * Work.KT.Psi.Cp S lam * Work.KT.Psi.orb3 S e)
      = Work.KT.Psi.clsM (Work.KT.Psi.SQ S) (X * e) := by
  have hc3 : (lam⁻¹)^3 = 1 := by rw [inv_pow, hlam, inv_one]
  -- the two factors of the product commute
  have hcomm : Cp S lam * orb3 S e = orb3 S e * Cp S lam := by
    rw [clsM_orb3_Cp (S := S) (A := A) lam]
    have hqe : (1 + algebraMap ℂ (Matrix (SQ S) (SQ S) A) lam⁻¹ * uPerm A S +
          algebraMap ℂ (Matrix (SQ S) (SQ S) A) (lam⁻¹ ^ 2) * (uPerm A S * uPerm A S))
          * orb3 S e
        = orb3 S e * (1 + algebraMap ℂ (Matrix (SQ S) (SQ S) A) lam⁻¹ * uPerm A S +
          algebraMap ℂ (Matrix (SQ S) (SQ S) A) (lam⁻¹ ^ 2) * (uPerm A S * uPerm A S)) := by
      rw [orb3]
      exact clsM_orb3_Qform e (uPerm A S) lam⁻¹ hc3 hu
    conv_lhs => rw [mul_assoc, hqe, ← mul_assoc, Algebra.commutes (1/3) (orb3 S e), mul_assoc]
  -- reorder the product into the shape produced by `cyclic_core`
  have h1 : X * Cp S lam * orb3 S e
      = X * (e + uPerm A S * e * (uPerm A S * uPerm A S)
              + (uPerm A S * uPerm A S) * e * uPerm A S)
        * (algebraMap ℂ (Matrix (SQ S) (SQ S) A) (1/3) *
          (1 + algebraMap ℂ (Matrix (SQ S) (SQ S) A) lam⁻¹ * uPerm A S +
            algebraMap ℂ (Matrix (SQ S) (SQ S) A) (lam⁻¹ ^ 2) * (uPerm A S * uPerm A S))) := by
    conv_lhs => rw [mul_assoc, hcomm, ← mul_assoc]
    rw [orb3, clsM_orb3_Cp (S := S) (A := A) lam]
  rw [h1]
  obtain ⟨hc1, hc2, hc3'⟩ :=
    Work.KT.PsiC.cyclic_core X e (uPerm A S) lam hX he hu hXe hXu heu heu2 hlam
  have hxe : (X * e) * (X * e) = X * e := by
    calc (X * e) * (X * e) = X * (e * X) * e := by noncomm_ring
      _ = X * (X * e) * e := by rw [← hXe]
      _ = (X * X) * (e * e) := by noncomm_ring
      _ = X * e := by rw [hX, he]
  exact clsM_orb3_mvN hc3' hxe ⟨_, _, hc1, hc2⟩

end

end Work.KT.Psi
