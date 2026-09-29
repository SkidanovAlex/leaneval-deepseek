import Mathlib
import Submission.Work.ZeroEst.ratdep
import Submission.Work.ZeroEst.fundamental_solution
import Submission.Work.ZeroEst.mderiv_adjugate_mul
import Submission.Work.ZeroEst.ps_eq_C_mul_of_deriv_mul
import Submission.Work.ZeroEst.det_mul_eq_sum_minors
import Submission.Work.ZeroEst.exists_det_submatrix_ne_zero
import Submission.Work.ZeroEst.subP_orbit
import Submission.Work.ZeroEstB.cramer_ratio
import Submission.Work.ZeroEstB.minor_det_prop
import Submission.Work.ZeroEstB.psi_ode

/-!
# `Work.ZeroEst.bounded_basis`

Lang's Lemma 2.4 in "bounded basis" form: a `Λ`-stable `ℚ(x)`-subspace of `ℚ(x)^m` that is
spanned by polynomial rows admits a polynomial spanning set whose entries have degree bounded by a
constant depending only on `m`, `q` and `A`.

The proof expands at a rational point `a` with `q(a) ≠ 0`; the fundamental solution `Φ` of the
system turns the `Λ`-stability into a first order system for `P · Φ`, whose maximal minors are all
`ℚ`-proportional; Cauchy--Binet expresses the maximal minors of `P` in terms of them, and
`Work.ZeroEst.ratdep` then bounds the degrees of the resulting rational functions.
-/

namespace Work.ZeroEst

open Polynomial PowerSeries Matrix

noncomputable section

/-! ## Auxiliary lemmas -/

/-- A nonzero polynomial over `ℚ` does not vanish at every rational point. -/
lemma exists_eval_ne_zero (q : Polynomial ℚ) (hq : q ≠ 0) : ∃ a : ℚ, q.eval a ≠ 0 := by
  by_contra h
  push Not at h
  refine hq (Polynomial.eq_zero_of_infinite_isRoot q ?_)
  refine Set.Infinite.mono (fun x _ => ?_) Set.infinite_univ
  exact (Polynomial.IsRoot.def).mpr (h x)

lemma natDegree_comp_X_sub_C (a : ℚ) (p : Polynomial ℚ) :
    (p.comp (Polynomial.X - Polynomial.C a)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, Nat.mul_one]

lemma natDegree_comp_X_add_C (a : ℚ) (p : Polynomial ℚ) :
    (p.comp (Polynomial.X + Polynomial.C a)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, Nat.mul_one]

/-- The substitution `p ↦ p(x + a)` as a ring hom `ℚ[X] → ℚ[X]`. -/
def compShift (a : ℚ) : Polynomial ℚ →+* Polynomial ℚ :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C a)

lemma compShift_eq (a : ℚ) (p : Polynomial ℚ) :
    compShift a p = p.comp (Polynomial.X + Polynomial.C a) := by
  have h : compShift a = Polynomial.compRingHom (Polynomial.X + Polynomial.C a) := by
    refine Polynomial.ringHom_ext ?_ ?_
    · intro x; simp [compShift]
    · simp [compShift, Polynomial.compRingHom]
  rw [h]; rfl

/-- The substitution `p ↦ p(x + a)` viewed in `ℚ⟦X⟧`. -/
def substPS (a : ℚ) : Polynomial ℚ →+* PowerSeries ℚ :=
  Polynomial.coeToPowerSeries.ringHom.comp (compShift a)

lemma substPS_eq (a : ℚ) (p : Polynomial ℚ) :
    substPS a p = ((p.comp (Polynomial.X + Polynomial.C a) : Polynomial ℚ) : PowerSeries ℚ) := by
  rw [substPS, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, compShift_eq]

lemma substPS_injective (a : ℚ) : Function.Injective (substPS a) := by
  intro p q h
  rw [substPS_eq, substPS_eq] at h
  have h2 : p.comp (Polynomial.X + Polynomial.C a) = q.comp (Polynomial.X + Polynomial.C a) :=
    Polynomial.coe_injective ℚ h
  have h3 : (p - q).comp (Polynomial.X + Polynomial.C a) = 0 := by
    rw [Polynomial.sub_comp, h2, sub_self]
  exact sub_eq_zero.mp (Polynomial.comp_X_add_C_eq_zero_iff.mp h3)

/-- The Taylor expansion at `a`, as a ring hom `ℚ(x) → Frac ℚ⟦X⟧`. -/
def epsilon (a : ℚ) : RatFunc ℚ →+* FractionRing (PowerSeries ℚ) :=
  IsFractionRing.lift
    (g := (algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))).comp (substPS a))
    ((IsFractionRing.injective (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))).comp
      (substPS_injective a))

lemma epsilon_algebraMap (a : ℚ) (p : Polynomial ℚ) :
    epsilon a (algebraMap (Polynomial ℚ) (RatFunc ℚ) p)
      = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (substPS a p) := by
  simp only [epsilon, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

lemma epsilon_injective (a : ℚ) : Function.Injective (epsilon a) := fun _ _ h =>
  RingHom.injective _ h

/-- The `ℚ`-span of all products of at most `m` entries of the matrix `M`. -/
def prodSpan {m : ℕ} (M : Fin m → Fin m → PowerSeries ℚ) : Submodule ℚ (PowerSeries ℚ) :=
  Submodule.span ℚ (Set.range fun p : (d : Fin (m+1)) × (Fin (d : ℕ) → Fin m × Fin m) =>
    ∏ l : Fin (p.1 : ℕ), M (p.2 l).1 (p.2 l).2)

lemma finiteDimensional_prodSpan {m : ℕ} (M : Fin m → Fin m → PowerSeries ℚ) :
    FiniteDimensional ℚ (prodSpan M) :=
  FiniteDimensional.span_of_finite ℚ (Set.finite_range _)

lemma prod_mem_prodSpan {m r : ℕ} (M : Fin m → Fin m → PowerSeries ℚ) (hr : r ≤ m)
    (T I : Fin r → Fin m) : ∏ b : Fin r, M (T b) (I b) ∈ prodSpan M := by
  refine Submodule.subset_span ⟨⟨⟨r, Nat.lt_succ_of_le hr⟩, fun l => (T l, I l)⟩, ?_⟩
  rfl

lemma submatrix_mul_id {R : Type*} [Semiring R] {r m : ℕ} (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin r) (Fin m) R) (I : Fin r → Fin m) :
    (A * B).submatrix id I = A * B.submatrix id I := by
  ext a b; simp [Matrix.mul_apply, Matrix.submatrix_apply]

/-- The determinant of a matrix whose columns are given by a non-injective map vanishes. -/
lemma det_submatrix_eq_zero_of_not_injective {R : Type*} [CommRing R] {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) R) (j : Fin r → Fin m) (hj : ¬ Function.Injective j) :
    (A.submatrix id j).det = 0 := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hj
  refine Matrix.det_zero_of_column_eq hne (fun k => ?_)
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab]

/-- Cauchy--Binet in the "column" form: the determinant of `E * Y` is the sum over all column
choices `j` of the determinant of the minor of `E` selected by `j` times the product of the
corresponding entries of `Y`. -/
theorem cauchy_binet_cols {r m : ℕ} (E : Matrix (Fin r) (Fin m) (PowerSeries ℚ))
    (Y : Matrix (Fin m) (Fin r) (PowerSeries ℚ)) :
    (E * Y).det = ∑ j : Fin r → Fin m,
      (Matrix.of (fun a b : Fin r => E a (j b))).det * ∏ b : Fin r, Y (j b) b := by
  have h := det_mul_eq_sum_minors (E := Yᵀ) (Y := Eᵀ)
  rw [← Matrix.transpose_mul] at h
  rw [Matrix.det_transpose (E * Y)] at h
  rw [h]
  refine Finset.sum_congr rfl fun T _ => ?_
  have h1 : (∏ a : Fin r, Yᵀ a (T a)) = ∏ b : Fin r, Y (T b) b := by
    refine Finset.prod_congr rfl fun b _ => ?_
    simp [Matrix.transpose_apply]
  have h2 : (Eᵀ.submatrix T id).det = (Matrix.of (fun a b : Fin r => E a (T b))).det := by
    have hh : Eᵀ.submatrix T id = (Matrix.of (fun a b : Fin r => E a (T b)))ᵀ := by
      ext a b; simp [Matrix.submatrix_apply, Matrix.transpose_apply]
    rw [hh, Matrix.det_transpose]
  rw [h1, h2, mul_comm]

/-- Lang's Lemma 2.4 in "bounded basis" form. -/
theorem bounded_basis (m : ℕ) (q : Polynomial ℚ) (hq : q ≠ 0) (A : Fin m → Fin m → Polynomial ℚ) :
    ∃ c : ℕ, ∀ (r : ℕ) (P : Fin r → Fin m → Polynomial ℚ),
      LinearIndependent (RatFunc ℚ) (fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (P k j)) →
      (∀ k, (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
          (q * Polynomial.derivative (P k j) + ∑ i, P k i * A i j)) ∈
        Submodule.span (RatFunc ℚ) (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (P k j))) →
      ∃ v : Fin r → Fin m → Polynomial ℚ, (∀ i j, (v i j).natDegree ≤ c) ∧
        Submodule.span (RatFunc ℚ) (Set.range fun i => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j)) =
          Submodule.span (RatFunc ℚ) (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (P k j)) := by
  classical
  obtain ⟨a, ha⟩ := exists_eval_ne_zero q hq
  set qs : Polynomial ℚ := q.comp (Polynomial.X + Polynomial.C a) with hqsdef
  set As : Fin m → Fin m → Polynomial ℚ :=
    fun i j => (A i j).comp (Polynomial.X + Polynomial.C a) with hAsdef
  have hqs0 : qs.coeff 0 ≠ 0 := by
    rw [hqsdef, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
    simpa using ha
  obtain ⟨Phi, _hPhi0, hPhiODE, hPhiUnit⟩ := fundamental_solution m qs As hqs0
  set Phiinv : Matrix (Fin m) (Fin m) (PowerSeries ℚ) := Phi⁻¹ with hPhiinvdef
  have hPhiMul : Phi * Phiinv = 1 := by
    rw [hPhiinvdef, Matrix.mul_nonsing_inv]; exact hPhiUnit
  have hPhiMul' : Phiinv * Phi = 1 := by
    rw [hPhiinvdef, Matrix.nonsing_inv_mul]; exact hPhiUnit
  haveI := finiteDimensional_prodSpan (fun i j => Phiinv i j)
  obtain ⟨N0, hN0⟩ := ratdep (prodSpan (fun i j => Phiinv i j))
  refine ⟨m * N0, ?_⟩
  intro r P hLI hspan
  by_cases hr0 : r = 0
  · subst hr0
    let v0 : Fin 0 → Fin m → Polynomial ℚ := fun i => Fin.elim0 i
    refine ⟨v0, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · have h1 : Submodule.span (RatFunc ℚ)
          (Set.range fun i : Fin 0 => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v0 i j)) = ⊥ := by
        rw [Submodule.span_eq_bot]; rintro x ⟨i, rfl⟩; exact Fin.elim0 i
      have h2 : Submodule.span (RatFunc ℚ)
          (Set.range fun i : Fin 0 => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (P i j)) = ⊥ := by
        rw [Submodule.span_eq_bot]; rintro x ⟨i, rfl⟩; exact Fin.elim0 i
      rw [h1, h2]
  · -- main case 1 ≤ r
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    set A0 : Fin r → Fin m → RatFunc ℚ :=
      fun k j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (P k j) with hA0def
    have hLI' : LinearIndependent (RatFunc ℚ) (Matrix.of A0).row := hLI
    have hrank : (Matrix.of A0).rank = r := by
      rw [LinearIndependent.rank_matrix hLI', Fintype.card_fin]
    obtain ⟨I, hIinj, hIdet⟩ := exists_det_submatrix_ne_zero (Matrix.of A0) hrank
    -- the coefficients expressing `Lam q A (P k)` in the span of the `P l`
    have hμexists : ∀ k, ∃ c : Fin r → RatFunc ℚ, ∑ l, c l • A0 l
        = (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Lam q A (P k)) j)) := by
      intro k
      exact (Submodule.mem_span_range_iff_exists_fun (RatFunc ℚ)).mp (hspan k)
    choose μ hμspec using hμexists
    have hμmat : (Matrix.of μ : Matrix (Fin r) (Fin r) (RatFunc ℚ)) * (Matrix.of A0)
        = Matrix.of (fun k j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Lam q A (P k)) j)) := by
      ext k j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      have h := congr_fun (hμspec k) j
      rw [Finset.sum_apply] at h
      simpa [Pi.smul_apply, smul_eq_mul] using h

    -- ---------- the polynomial first order relation satisfied by `LamP` ----------
    set Pmat : Matrix (Fin r) (Fin m) (Polynomial ℚ) := Matrix.of (fun k j => P k j) with hPmatdef
    set LamP : Matrix (Fin r) (Fin m) (Polynomial ℚ) :=
      Matrix.of (fun k j => Lam q A (P k) j) with hLamPdef
    set Bpoly : Matrix (Fin r) (Fin r) (Polynomial ℚ) := Pmat.submatrix id I with hBpolydef
    set s : Polynomial ℚ := Bpoly.det with hsdef
    set Nmat : Matrix (Fin r) (Fin r) (Polynomial ℚ) := LamP.submatrix id I * Bpoly.adjugate
      with hNmatdef
    have hBK : (Matrix.of A0).submatrix id I
        = (algebraMap (Polynomial ℚ) (RatFunc ℚ)).mapMatrix Bpoly := by
      rw [hBpolydef, hPmatdef]; ext k l; rfl
    have hs_ne : s ≠ 0 := by
      intro hs0
      apply hIdet
      rw [hBK, ← RingHom.map_det, ← hsdef, hs0, map_zero]
    have hLamK : LamP.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))
        = Matrix.of (fun k j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Lam q A (P k)) j)) := by
      rw [hLamPdef]; ext k j; rfl
    have hμmat' : (Matrix.of μ : Matrix (Fin r) (Fin r) (RatFunc ℚ)) * (Matrix.of A0)
        = LamP.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
      rw [hμmat, hLamK]
    have hμBK : (Matrix.of μ : Matrix (Fin r) (Fin r) (RatFunc ℚ))
          * ((algebraMap (Polynomial ℚ) (RatFunc ℚ)).mapMatrix Bpoly)
        = (LamP.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).submatrix id I := by
      rw [← hBK, ← submatrix_mul_id, hμmat']
    have hLamSub : (algebraMap (Polynomial ℚ) (RatFunc ℚ)).mapMatrix (LamP.submatrix id I)
        = (LamP.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).submatrix id I := by
      ext k l; rfl
    have hNB : (algebraMap (Polynomial ℚ) (RatFunc ℚ)).mapMatrix Nmat
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) s
          • (Matrix.of μ : Matrix (Fin r) (Fin r) (RatFunc ℚ)) := by
      rw [hNmatdef, RingHom.map_mul, RingHom.map_adjugate, hLamSub, ← hμBK, Matrix.mul_assoc,
        Matrix.mul_adjugate, ← RingHom.map_det, ← hsdef, Matrix.mul_smul, Matrix.mul_one]
    have hkeyK : algebraMap (Polynomial ℚ) (RatFunc ℚ) s
          • (Matrix.of (fun k j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Lam q A (P k)) j)))
        = (algebraMap (Polynomial ℚ) (RatFunc ℚ)).mapMatrix Nmat * Matrix.of A0 := by
      rw [← hLamK, ← hμmat', ← Matrix.smul_mul, ← hNB]
    have hkeyEP : ∀ k j, algebraMap (Polynomial ℚ) (RatFunc ℚ) s
          * algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Lam q A (P k)) j)
        = ∑ l, algebraMap (Polynomial ℚ) (RatFunc ℚ) (Nmat k l)
            * algebraMap (Polynomial ℚ) (RatFunc ℚ) (P l j) := by
      intro k j
      have h := congr_fun (congr_fun hkeyK k) j
      simpa only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply,
        RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hPmatdef, hA0def] using h
    have hkey : ∀ k j, s * Lam q A (P k) j = ∑ l, Nmat k l * P l j := by
      intro k j
      apply IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)
      simpa only [map_mul, map_sum] using hkeyEP k j
    -- ---------- the power series side ----------
    set Pc : Fin r → Fin m → Polynomial ℚ :=
      fun k j => (P k j).comp (Polynomial.X + Polynomial.C a) with hPcdef
    set sc : Polynomial ℚ := s.comp (Polynomial.X + Polynomial.C a) with hscdef
    set Nc : Fin r → Fin r → Polynomial ℚ :=
      fun k l => (Nmat k l).comp (Polynomial.X + Polynomial.C a) with hNcdef
    set Psub : Matrix (Fin r) (Fin m) (PowerSeries ℚ) := Pmat.map (substPS a) with hPsubdef
    set Psi : Matrix (Fin r) (Fin m) (PowerSeries ℚ) := Psub * Phi with hPsidef
    have hsc_eq : (sc : PowerSeries ℚ) = substPS a s := by rw [hscdef, substPS_eq]
    have hNc_eq : ∀ k l, (Nc k l : PowerSeries ℚ) = substPS a (Nmat k l) := by
      intro k l; rw [hNcdef, substPS_eq]
    have hPc_eq : ∀ l j, (Pc l j : PowerSeries ℚ) = substPS a (P l j) := by
      intro l j; rw [hPcdef, substPS_eq]
    have hLamComp : ∀ k j, (Lam q A (P k) j).comp (Polynomial.X + Polynomial.C a)
        = (Lam qs As (Pc k)) j := by
      intro k j
      have h := (congr_fun (subP_Lam a q A (P k)) j).symm
      have h1 : subP a q = qs := by rw [hqsdef]; exact subP_apply a q
      have h2 : (fun i j => subP a (A i j)) = As := by
        funext i j; rw [hAsdef]; exact subP_apply a (A i j)
      have h3 : (fun i => subP a (P k i)) = Pc k := by
        funext i; rw [hPcdef]; exact subP_apply a (P k i)
      rw [subP_apply a (Lam q A (P k) j), h1, h2, h3] at h
      exact h
    have hLam_eq : ∀ k j, ((Lam qs As (Pc k)) j : PowerSeries ℚ)
        = substPS a (Lam q A (P k) j) := by
      intro k j; rw [← hLamComp k j, substPS_eq]
    have hNpsi : ∀ k j, (sc : PowerSeries ℚ) * ((Lam qs As (Pc k)) j : PowerSeries ℚ)
        = ∑ l, (Nc k l : PowerSeries ℚ) * (Pc l j : PowerSeries ℚ) := by
      intro k j
      rw [hsc_eq, hLam_eq k j]
      simp only [hNc_eq, hPc_eq]
      have h := congrArg (substPS a) (hkey k j)
      simpa only [map_mul, map_sum] using h
    have hPsiODE : ((sc : PowerSeries ℚ) * (qs : PowerSeries ℚ)) • mderiv Psi
        = Nmat.map (substPS a) * Psi := by
      have h := Work.ZeroEstB.psi_ode qs As Pc Phi sc Nc hPhiODE hNpsi
      have e1 : Matrix.of (fun k j => ((Pc k j : Polynomial ℚ) : PowerSeries ℚ)) = Psub := by
        rw [hPsubdef, hPmatdef]
        funext k j
        simp only [Matrix.of_apply, Matrix.map_apply]
        exact hPc_eq k j
      have e2 : Matrix.of (fun k l => ((Nc k l : Polynomial ℚ) : PowerSeries ℚ))
          = Nmat.map (substPS a) := by
        funext k l
        simp only [Matrix.of_apply, Matrix.map_apply]
        exact hNc_eq k l
      rw [e1, e2] at h
      rw [hPsidef]
      exact h
    -- ---------- Cauchy--Binet and the maximal minors of `Psi` ----------
    have hPsiInv : Psi * Phiinv = Psub := by
      rw [hPsidef, Matrix.mul_assoc, hPhiMul, Matrix.mul_one]
    have hCBgen : ∀ I' : Fin r → Fin m, (Psub.submatrix id I').det
        = ∑ j : Fin r → Fin m, (Psi.submatrix id j).det
            * ∏ b : Fin r, Phiinv (j b) (I' b) := by
      intro I'
      have h1 : Psub.submatrix id I' = Psi * (Phiinv.submatrix (id : Fin m → Fin m) I') := by
        rw [← hPsiInv]
        funext k b
        simp [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [h1, cauchy_binet_cols]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hf : (Matrix.of (fun a b : Fin r => Psi a (j b))) = Psi.submatrix id j := rfl
      have hg : (∏ b : Fin r, (Phiinv.submatrix (id : Fin m → Fin m) I') (j b) b)
          = ∏ b : Fin r, Phiinv (j b) (I' b) := by
        refine Finset.prod_congr rfl fun b _ => ?_
        simp [Matrix.submatrix_apply]
      rw [hf, hg]
    have hPsubBpoly : Psub.submatrix id I = (substPS a).mapMatrix Bpoly := by
      rw [hPsubdef, hPmatdef, hBpolydef]
      funext k b
      simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply]
      rfl
    have hPsubdet : (Psub.submatrix id I).det ≠ 0 := by
      rw [hPsubBpoly, ← RingHom.map_det, ← hsdef]
      intro h
      exact hs_ne (substPS_injective a (by rw [h, map_zero]))
    obtain ⟨T0, hT0⟩ : ∃ j : Fin r → Fin m, (Psi.submatrix id j).det ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hPsubdet ?_
      rw [hCBgen I]
      exact Finset.sum_eq_zero fun j _ => by rw [hcon j, zero_mul]
    have hrm : r ≤ m := by
      have h := Matrix.rank_le_width (Matrix.of A0)
      rw [hrank] at h
      exact h
    have hsq_ne : (sc : PowerSeries ℚ) * (qs : PowerSeries ℚ) ≠ 0 := by
      rw [mul_ne_zero_iff]
      refine ⟨?_, ?_⟩
      · rw [hsc_eq]
        intro h
        exact hs_ne (substPS_injective a (by rw [h, map_zero]))
      · intro h
        exact hqs0 (by simpa using congrArg (PowerSeries.coeff 0) h)
    set M0 : PowerSeries ℚ := (Psi.submatrix id T0).det with hM0def
    have hM0_ne : M0 ≠ 0 := hT0
    have hprop : ∀ j : Fin r → Fin m, ∃ c : ℚ, (Psi.submatrix id j).det = PowerSeries.C c * M0 := by
      intro j
      exact Work.ZeroEstB.minor_det_prop ((sc : PowerSeries ℚ) * (qs : PowerSeries ℚ)) Psi
        (Nmat.map (substPS a)) hsq_ne hPsiODE T0 hT0 j
    choose lam hlam using hprop
    let phi : (Fin r → Fin m) → PowerSeries ℚ := fun I' =>
      ∑ j : {j : Fin r → Fin m // Function.Injective j},
        (lam (j : Fin r → Fin m)) • ∏ b : Fin r, Phiinv ((j : Fin r → Fin m) b) (I' b)
    have hphi_mem : ∀ I', phi I' ∈ prodSpan (fun i j => Phiinv i j) := by
      intro I'
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
      exact prod_mem_prodSpan _ hrm (j : Fin r → Fin m) I'
    have hphi_eq : ∀ I' : Fin r → Fin m, (Psub.submatrix id I').det = M0 * phi I' := by
      intro I'
      rw [hCBgen I']
      have hsum : (∑ j : Fin r → Fin m, (Psi.submatrix id j).det * ∏ b, Phiinv (j b) (I' b))
          = ∑ j : {j : Fin r → Fin m // Function.Injective j},
              (Psi.submatrix id (j : Fin r → Fin m)).det
                * ∏ b, Phiinv ((j : Fin r → Fin m) b) (I' b) := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin r → Fin m => Function.Injective j)]
        have hzero : (∑ j : {j : Fin r → Fin m // ¬ Function.Injective j},
            (Psi.submatrix id (j : Fin r → Fin m)).det
              * ∏ b, Phiinv ((j : Fin r → Fin m) b) (I' b)) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [det_submatrix_eq_zero_of_not_injective (A := Psi) (j : Fin r → Fin m) j.2, zero_mul]
        rw [hzero, add_zero]
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hlam (j : Fin r → Fin m), PowerSeries.smul_eq_C_mul]
      ring
    have hphi_ne : phi I ≠ 0 := by
      intro h0
      refine hPsubdet ?_
      rw [hphi_eq I, h0, mul_zero]

    -- ---------- Cramer's rule and Lang's Lemma 2.2 ----------
    let Bupd : Fin r → Fin m → Matrix (Fin r) (Fin r) (Polynomial ℚ) :=
      fun i j => Matrix.of (fun k b => P k (Function.update I i j b))
    let Abi : Fin r → Fin m → Polynomial ℚ := fun i j => (Bupd i j).det
    let Ac : Fin r → Fin m → Polynomial ℚ := fun i j => (Abi i j).comp (Polynomial.X + Polynomial.C a)
    set e : Matrix (Fin r) (Fin m) (RatFunc ℚ) :=
      ((Matrix.of A0).submatrix id I)⁻¹ * Matrix.of A0 with hedef
    have halg_ne : ∀ {x : PowerSeries ℚ}, x ≠ 0 →
        algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) x ≠ 0 := by
      intro x hx h
      exact hx (IsFractionRing.injective (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
        (by rw [h, map_zero]))
    have hPsubBupd : ∀ i j, Psub.submatrix id (Function.update I i j)
        = (substPS a).mapMatrix (Bupd i j) := by
      intro i j
      rw [hPsubdef, hPmatdef]
      funext k b
      simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply]
      rfl
    have hBupd_map : ∀ i j, (Matrix.of A0).submatrix id (Function.update I i j)
        = (algebraMap (Polynomial ℚ) (RatFunc ℚ)).mapMatrix (Bupd i j) := by
      intro i j; funext k b; rfl
    have hBKdet : ((Matrix.of A0).submatrix id I).det
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) s := by
      rw [hBK, ← RingHom.map_det, ← hsdef]
    have hCramer : ∀ i j, e i j = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Abi i j)
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) s := by
      intro i j
      rw [hedef, Work.ZeroEstB.cramer_ratio (Matrix.of A0) I hIdet i j, hBupd_map i j,
        ← RingHom.map_det, hBKdet]
    have hsc_ne : sc ≠ 0 := by
      rw [hscdef]
      intro h
      exact hs_ne (Polynomial.comp_X_add_C_eq_zero_iff.mp h)
    have hs_alg_ne : algebraMap (Polynomial ℚ) (RatFunc ℚ) s ≠ 0 := fun h =>
      hs_ne (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) (by rw [h, map_zero]))
    have hCramer_mul : ∀ i j, e i j * algebraMap (Polynomial ℚ) (RatFunc ℚ) s
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Abi i j) := by
      intro i j
      rw [hCramer i j, div_mul_cancel₀ _ hs_alg_ne]
    have hCramer_eps : ∀ i j, epsilon a (e i j)
          * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) sc
        = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (Ac i j) := by
      intro i j
      have h := congrArg (epsilon a) (hCramer_mul i j)
      rw [map_mul, epsilon_algebraMap, epsilon_algebraMap, ← hsc_eq, substPS_eq] at h
      exact h
    have hAbi_eps : ∀ i j, substPS a (Abi i j) = M0 * phi (Function.update I i j) := by
      intro i j
      have h := hphi_eq (Function.update I i j)
      rw [hPsubBupd i j, ← RingHom.map_det] at h
      exact h
    have hs_eps : substPS a s = M0 * phi I := by
      have h := hphi_eq I
      rw [hPsubBpoly, ← RingHom.map_det, ← hsdef] at h
      exact h
    have hAc_eps : ∀ i j, (Ac i j : PowerSeries ℚ) = M0 * phi (Function.update I i j) := by
      intro i j
      rw [show Ac i j = (Abi i j).comp (Polynomial.X + Polynomial.C a) from rfl,
        ← substPS_eq, hAbi_eps i j]
    have hsc_eps : (sc : PowerSeries ℚ) = M0 * phi I := by
      rw [hsc_eq, hs_eps]
    have he_eps : ∀ i j, epsilon a (e i j)
        = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi (Function.update I i j))
          / algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I) := by
      intro i j
      rw [eq_div_iff (halg_ne hphi_ne)]
      have hk : epsilon a (e i j)
          * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I)
          = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
              (phi (Function.update I i j)) := by
        have hm := hCramer_eps i j
        rw [hAc_eps i j, hsc_eps, map_mul, map_mul] at hm
        refine mul_left_cancel₀ (halg_ne hM0_ne) ?_
        rw [← mul_assoc, mul_comm (algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) M0)
          (epsilon a (e i j)), mul_assoc]
        exact hm
      exact hk
    have hPSrel : ∀ i j, (sc : PowerSeries ℚ) * phi (Function.update I i j)
        = (Ac i j : PowerSeries ℚ) * phi I := by
      intro i j
      apply IsFractionRing.injective (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
      rw [map_mul, map_mul]
      have hmain : algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
            (phi (Function.update I i j))
            * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) sc
          = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I)
            * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (Ac i j) := by
        have hk : epsilon a (e i j)
            * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I)
            = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
                (phi (Function.update I i j)) := by
          rw [he_eps i j, div_mul_cancel₀ _ (halg_ne hphi_ne)]
        calc _ = epsilon a (e i j)
                * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I)
                * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) sc := by
              rw [← hk]
          _ = (epsilon a (e i j)
                * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) sc)
                * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I) := by ring
          _ = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (Ac i j)
                * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I) := by
              rw [hCramer_eps i j]
          _ = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I)
                * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (Ac i j) := by ring
      calc algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) sc
            * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi (Function.update I i j))
          = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi (Function.update I i j))
            * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) sc := by ring
        _ = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I)
            * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (Ac i j) := hmain
        _ = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (Ac i j)
            * algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (phi I) := by ring
    -- Lang's Lemma 2.2
    have hrat : ∀ i j, ∃ (P Q : Polynomial ℚ), P.degree ≤ (N0 : WithBot ℕ)
        ∧ Q.degree ≤ (N0 : WithBot ℕ) ∧ Q ≠ 0
        ∧ (Q : PowerSeries ℚ) * phi (Function.update I i j) = (P : PowerSeries ℚ) * phi I := by
      intro i j
      exact hN0 (phi (Function.update I i j)) (phi I) (hphi_mem _) (hphi_mem I) hphi_ne
        ⟨Ac i j, sc, hsc_ne, hPSrel i j⟩
    choose P0 Q0 hprops using hrat
    let R : Fin r → Fin m → Polynomial ℚ :=
      fun i j => (P0 i j).comp (Polynomial.X + Polynomial.C (-a))
    let S : Fin r → Fin m → Polynomial ℚ :=
      fun i j => (Q0 i j).comp (Polynomial.X + Polynomial.C (-a))
    have hS_ne : ∀ i j, S i j ≠ 0 := by
      intro i j
      rw [show S i j = (Q0 i j).comp (Polynomial.X + Polynomial.C (-a)) from rfl]
      intro h
      exact (hprops i j).2.2.1 (Polynomial.comp_X_add_C_eq_zero_iff.mp h)
    have hR_sub : ∀ i j, substPS a (R i j) = (P0 i j : PowerSeries ℚ) := by
      intro i j
      rw [show R i j = (P0 i j).comp (Polynomial.X + Polynomial.C (-a)) from rfl, substPS_eq,
        Polynomial.comp_assoc]
      simp
    have hS_sub : ∀ i j, substPS a (S i j) = (Q0 i j : PowerSeries ℚ) := by
      intro i j
      rw [show S i j = (Q0 i j).comp (Polynomial.X + Polynomial.C (-a)) from rfl, substPS_eq,
        Polynomial.comp_assoc]
      simp
    have heRS : ∀ i j, e i j * algebraMap (Polynomial ℚ) (RatFunc ℚ) (S i j)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (R i j) := by
      intro i j
      have hQ0ne : (Q0 i j : PowerSeries ℚ) ≠ 0 := fun h =>
        (hprops i j).2.2.1 (Polynomial.coe_injective ℚ h)
      have hrel : (Q0 i j : PowerSeries ℚ) * phi (Function.update I i j)
          = (P0 i j : PowerSeries ℚ) * phi I := (hprops i j).2.2.2
      have hdiv : epsilon a (e i j)
          = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (P0 i j)
            / algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (Q0 i j) := by
        rw [he_eps i j, div_eq_div_iff (halg_ne hphi_ne) (halg_ne hQ0ne)]
        rw [← map_mul, ← map_mul, mul_comm, hrel]
      have hgoal : epsilon a (algebraMap (Polynomial ℚ) (RatFunc ℚ) (R i j))
            / epsilon a (algebraMap (Polynomial ℚ) (RatFunc ℚ) (S i j)) = epsilon a (e i j) := by
        rw [hdiv, epsilon_algebraMap, epsilon_algebraMap, hR_sub i j, hS_sub i j]
      have heq : algebraMap (Polynomial ℚ) (RatFunc ℚ) (R i j)
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (S i j) = e i j := by
        apply epsilon_injective a
        rw [map_div₀]
        exact hgoal
      rw [← heq, div_mul_cancel₀ _ (fun h => hS_ne i j
        (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) (by rw [h, map_zero])))]

    -- ---------- assembling the answer ----------
    have hm1 : 1 ≤ m := by omega
    have hSdeg : ∀ i j', (S i j').natDegree ≤ N0 := by
      intro i j'
      rw [show S i j' = (Q0 i j').comp (Polynomial.X + Polynomial.C (-a)) from rfl,
        natDegree_comp_X_add_C]
      exact Polynomial.natDegree_le_iff_degree_le.mpr (hprops i j').2.1
    have hRdeg : ∀ i j, (R i j).natDegree ≤ N0 := by
      intro i j
      rw [show R i j = (P0 i j).comp (Polynomial.X + Polynomial.C (-a)) from rfl,
        natDegree_comp_X_add_C]
      exact Polynomial.natDegree_le_iff_degree_le.mpr (hprops i j).1
    have hproddeg : ∀ i j, (∏ j' ∈ Finset.univ.erase j, S i j').natDegree ≤ (m - 1) * N0 := by
      intro i j
      refine le_trans (Polynomial.natDegree_prod_le (Finset.univ.erase j)
        (fun j' => S i j')) ?_
      calc (∑ j' ∈ Finset.univ.erase j, (S i j').natDegree)
          ≤ ∑ j' ∈ Finset.univ.erase j, N0 :=
            Finset.sum_le_sum fun j' _ => hSdeg i j'
        _ = (Finset.univ.erase j).card * N0 := by rw [Finset.sum_const, smul_eq_mul]
        _ = (m - 1) * N0 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
              Fintype.card_fin]
    have hcoeff_ne : ∀ i, (∏ j : Fin m, algebraMap (Polynomial ℚ) (RatFunc ℚ) (S i j)) ≠ 0 := by
      intro i
      rw [Finset.prod_ne_zero_iff]
      intro j _
      exact fun h => hS_ne i j (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)
        (by rw [h, map_zero]))
    refine ⟨fun i j => R i j * ∏ j' ∈ Finset.univ.erase j, S i j', ?_, ?_⟩
    · intro i j
      refine le_trans Polynomial.natDegree_mul_le ?_
      have hR := hRdeg i j
      have hP := hproddeg i j
      have hmul2 : N0 + (m - 1) * N0 = m * N0 := by
        conv_rhs => rw [← Nat.sub_add_cancel hm1]
        rw [Nat.add_mul, one_mul, add_comm]
      omega
    · have hv_mul : ∀ i, (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
            (R i j * ∏ j' ∈ Finset.univ.erase j, S i j'))
          = (∏ j : Fin m, algebraMap (Polynomial ℚ) (RatFunc ℚ) (S i j)) • (fun j => e i j) := by
        intro i
        funext j
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [map_mul, map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
        rw [mul_assoc, mul_comm (algebraMap (Polynomial ℚ) (RatFunc ℚ) (S i j)) (e i j),
          ← heRS i j, mul_comm]
      have hv_inv : ∀ i, (fun j => e i j)
          = (∏ j : Fin m, algebraMap (Polynomial ℚ) (RatFunc ℚ) (S i j))⁻¹
            • (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
                (R i j * ∏ j' ∈ Finset.univ.erase j, S i j')) := by
        intro i
        rw [hv_mul i, smul_smul, inv_mul_cancel₀ (hcoeff_ne i), one_smul]
      have hspan_ve : Submodule.span (RatFunc ℚ)
            (Set.range fun i => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
              (R i j * ∏ j' ∈ Finset.univ.erase j, S i j'))
          = Submodule.span (RatFunc ℚ) (Set.range fun i => fun j => e i j) := by
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro x ⟨i, rfl⟩
          change (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
            (R i j * ∏ j' ∈ Finset.univ.erase j, S i j')) ∈ _
          rw [hv_mul i]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        · rw [Submodule.span_le]
          rintro x ⟨i, rfl⟩
          change (fun j => e i j) ∈ _
          rw [hv_inv i]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have he_row : ∀ i j, e i j
          = ∑ l, ((Matrix.of A0).submatrix id I)⁻¹ i l * A0 l j := by
        intro i j
        rw [hedef, Matrix.mul_apply]
        rfl
      have hPK_row : ∀ i j, A0 i j
          = ∑ l, ((Matrix.of A0).submatrix id I) i l * e l j := by
        intro i j
        have hmul : (Matrix.of A0) = ((Matrix.of A0).submatrix id I) * e := by
          rw [hedef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv, Matrix.one_mul]
          exact isUnit_iff_ne_zero.mpr hIdet
        have h := congr_fun (congr_fun hmul i) j
        rw [Matrix.mul_apply, Matrix.of_apply] at h
        exact h
      have hspan_ev : Submodule.span (RatFunc ℚ) (Set.range fun i => fun j => e i j)
          = Submodule.span (RatFunc ℚ) (Set.range fun i => fun j => A0 i j) := by
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro x ⟨i, rfl⟩
          change (fun j => e i j) ∈ _
          have hrow : (fun j => e i j)
              = ∑ l, ((Matrix.of A0).submatrix id I)⁻¹ i l • (fun j => A0 l j) := by
            funext j
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            exact he_row i j
          rw [hrow]
          exact Submodule.sum_mem _ fun l _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
        · rw [Submodule.span_le]
          rintro x ⟨i, rfl⟩
          change (fun j => A0 i j) ∈ _
          have hrow : (fun j => A0 i j)
              = ∑ l, ((Matrix.of A0).submatrix id I) i l • (fun j => e l j) := by
            funext j
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            exact hPK_row i j
          rw [hrow]
          exact Submodule.sum_mem _ fun l _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
      rw [hspan_ve, hspan_ev]

end

end Work.ZeroEst
