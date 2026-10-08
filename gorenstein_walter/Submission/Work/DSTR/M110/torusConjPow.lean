import Mathlib
import Submission.Work.DSTR.M110.nonsplitAux
import Submission.Work.DSTR.M110.SplitCase.GaloisPart
import Submission.Work.DSTR.M110.torusFrobDefs
import Submission.Work.DSTR.M110.torusFrobMain
import Submission.Work.DSTR.M110.companionConjProof
import Submission.Work.DSTR.M110.torusPermConjProof
import Submission.Work.DSTR.M110.wPartAux

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Polynomial Matrix

namespace Work.DSTR.M110

open Work.AUTL2

variable (p k : ℕ) [Fact p.Prime]

lemma pglImage_le_pgammaL (F : Type*) [Field F] [DecidableEq F] :
    pglImage F ≤ pgammaL F := le_sup_left

lemma galSub_le_pgammaL (F : Type*) [Field F] [DecidableEq F] :
    galSub F ≤ pgammaL F := le_sup_right


@[simp] lemma coe_GLmap (M : GL (Fin 2) (GaloisField p k)) :
    ((Matrix.GeneralLinearGroup.map (frobEquiv p k) M : GL (Fin 2) (GaloisField p k)) :
      Matrix (Fin 2) (Fin 2) (GaloisField p k)) =
      (M : Matrix (Fin 2) (Fin 2) (GaloisField p k)).map (frobEquiv p k) := rfl

/-- The "geometric Frobenius" element of `PΓL(2,q)`: conjugation by the companion
`!![0,c;1,0]`-Frobenius. -/
noncomputable def alpha [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c) :
    ↥(pgammaL (GaloisField p k)) :=
  ⟨pglHom (GaloisField p k)
        (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))) *
      galHom (GaloisField p k) (frobEquiv p k),
   Subgroup.mul_mem _
     (pglImage_le_pgammaL _ (MonoidHom.mem_range.mpr
       ⟨Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc)), rfl⟩))
     (galSub_le_pgammaL _ (MonoidHom.mem_range.mpr ⟨frobEquiv p k, rfl⟩))⟩

@[simp] lemma alpha_coe [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c) :
    (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) =
      pglHom (GaloisField p k)
          (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))) *
        galHom (GaloisField p k) (frobEquiv p k) := rfl

lemma galMap_galHom_aux [DecidableEq (GaloisField p k)] (σ : GaloisField p k ≃+* GaloisField p k)
    (h : galHom (GaloisField p k) σ ∈ pgammaL (GaloisField p k)) :
    SplitAux.galMap (GaloisField p k) ⟨galHom (GaloisField p k) σ, h⟩ = σ := by
  apply Galois.galHom_injective (GaloisField p k)
  rw [SplitAux.galMap_apply]
  exact SplitAux.galPart_unique (GaloisField p k) ⟨galHom (GaloisField p k) σ, h⟩
    (c := 1) (τ := galHom (GaloisField p k) σ) (Subgroup.one_mem _)
    (SplitAux.galSub_mem_galHom (GaloisField p k) σ) (by rw [one_mul])

lemma galMap_alpha [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c) :
    SplitAux.galMap (GaloisField p k) (alpha p k c hc) = frobEquiv p k := by
  have h1 : SplitAux.galMap (GaloisField p k)
      (⟨pglHom (GaloisField p k)
          (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))),
        pglImage_le_pgammaL _ (MonoidHom.mem_range.mpr
          ⟨Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc)), rfl⟩)⟩ :
        ↥(pgammaL (GaloisField p k))) = 1 :=
    SplitAux.galPart_of_mem (GaloisField p k) _
      (MonoidHom.mem_range.mpr
        ⟨Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc)), rfl⟩)
  have h2 : SplitAux.galMap (GaloisField p k)
      (⟨galHom (GaloisField p k) (frobEquiv p k),
        galSub_le_pgammaL _ (MonoidHom.mem_range.mpr ⟨frobEquiv p k, rfl⟩)⟩ :
        ↥(pgammaL (GaloisField p k))) = frobEquiv p k :=
    galMap_galHom_aux p k (frobEquiv p k) _
  calc SplitAux.galMap (GaloisField p k) (alpha p k c hc)
      = SplitAux.galMap (GaloisField p k)
          (⟨pglHom (GaloisField p k)
              (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))),
            pglImage_le_pgammaL _ (MonoidHom.mem_range.mpr
              ⟨Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc)), rfl⟩)⟩ *
          ⟨galHom (GaloisField p k) (frobEquiv p k),
            galSub_le_pgammaL _ (MonoidHom.mem_range.mpr ⟨frobEquiv p k, rfl⟩)⟩) := rfl
    _ = SplitAux.galMap (GaloisField p k)
          ⟨pglHom (GaloisField p k)
              (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))),
            pglImage_le_pgammaL _ (MonoidHom.mem_range.mpr
              ⟨Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc)), rfl⟩)⟩ *
        SplitAux.galMap (GaloisField p k)
          ⟨galHom (GaloisField p k) (frobEquiv p k),
            galSub_le_pgammaL _ (MonoidHom.mem_range.mpr ⟨frobEquiv p k, rfl⟩)⟩ := by
        rw [map_mul]
    _ = frobEquiv p k := by rw [h1, h2, one_mul]


lemma alpha_torusPerm [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c)
    (hodd : Odd p) (u : TorUnits (GaloisField p k) c) :
    (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) *
        torusPermB0 p k c hc u * (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k)))⁻¹ =
      torusPermB0 p k c hc (u ^ p) := by
  have hGL : deltaGL p k c (ne_zero_of_not_isSquare hc) *
        Matrix.GeneralLinearGroup.map (frobEquiv p k) (torusGLB0 p k c hc u) *
        (deltaGL p k c (ne_zero_of_not_isSquare hc))⁻¹ =
      torusGLB0 p k c hc (u ^ p) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv, deltaGL_coe, coe_GLmap, torusGLB0_apply_coe]
    rw [torusAlgHomFrob p k c hc hodd (u : _)]
    simp only [torusGLB0_apply_coe, Units.val_pow_eq_pow_val]
  have hconj := Galois.fieldAut_conj_pgl (GaloisField p k) (frobEquiv p k) (torusGLB0 p k c hc u)
  calc (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) * torusPermB0 p k c hc u *
        (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k)))⁻¹
      = (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))) *
            galHom (GaloisField p k) (frobEquiv p k)) *
          pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (torusGLB0 p k c hc u)) *
          (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))) *
            galHom (GaloisField p k) (frobEquiv p k))⁻¹ := by
        rw [alpha_coe, torusPermB0_eq]
    _ = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))) *
          (galHom (GaloisField p k) (frobEquiv p k) *
            pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (torusGLB0 p k c hc u)) *
            (galHom (GaloisField p k) (frobEquiv p k))⁻¹) *
          (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))))⁻¹ := by
        group
    _ = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))) *
          pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map (frobEquiv p k) (torusGLB0 p k c hc u))) *
          (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c (ne_zero_of_not_isSquare hc))))⁻¹ := by
        rw [hconj]
    _ = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk
          (deltaGL p k c (ne_zero_of_not_isSquare hc) *
            Matrix.GeneralLinearGroup.map (frobEquiv p k) (torusGLB0 p k c hc u) *
            (deltaGL p k c (ne_zero_of_not_isSquare hc))⁻¹)) := by
        simp only [map_mul, map_inv]
    _ = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (torusGLB0 p k c hc (u ^ p))) := by
        rw [hGL]
    _ = torusPermB0 p k c hc (u ^ p) := by rw [torusPermB0_eq]

lemma alpha_pow_torusPerm [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c)
    (hodd : Odd p) : ∀ (n : ℕ) (u : TorUnits (GaloisField p k) c),
    ((alpha p k c hc ^ n : ↥(pgammaL (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) *
        torusPermB0 p k c hc u *
        (((alpha p k c hc ^ n : ↥(pgammaL (GaloisField p k)))) :
          Equiv.Perm (P1 (GaloisField p k)))⁻¹ =
      torusPermB0 p k c hc (u ^ p ^ n) := by
  intro n
  induction n with
  | zero => intro u; simp
  | succ n ih =>
    intro u
    have hcoe : ((alpha p k c hc ^ (n + 1) : ↥(pgammaL (GaloisField p k))) :
        Equiv.Perm (P1 (GaloisField p k))) =
        ((alpha p k c hc ^ n : ↥(pgammaL (GaloisField p k))) :
          Equiv.Perm (P1 (GaloisField p k))) *
          (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) := by
      rw [pow_succ, Subgroup.coe_mul]
    rw [hcoe]
    rw [show ((alpha p k c hc ^ n : ↥(pgammaL (GaloisField p k))) :
            Equiv.Perm (P1 (GaloisField p k))) *
          (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) * torusPermB0 p k c hc u *
          (((alpha p k c hc ^ n : ↥(pgammaL (GaloisField p k))) :
            Equiv.Perm (P1 (GaloisField p k))) *
            (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))))⁻¹
        = ((alpha p k c hc ^ n : ↥(pgammaL (GaloisField p k))) :
            Equiv.Perm (P1 (GaloisField p k))) *
          ((alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) * torusPermB0 p k c hc u *
            (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k)))⁻¹) *
          (((alpha p k c hc ^ n : ↥(pgammaL (GaloisField p k))) :
            Equiv.Perm (P1 (GaloisField p k))))⁻¹ by group]
    rw [alpha_torusPerm p k c hc hodd u, ih (u ^ p)]
    congr 1
    rw [← pow_mul, ← pow_succ']


lemma alpha_comm_tB0 [DecidableEq (GaloisField p k)] (c : GaloisField p k) (hc : ¬ IsSquare c)
    (hodd : Odd p) :
    (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) * tB0 p k c hc =
      tB0 p k c hc * (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) := by
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have hkey : Matrix.ProjGenLinGroup.mk (deltaGL p k c hc0 *
        Matrix.GeneralLinearGroup.map (frobEquiv p k) (B0 c hc) *
        (deltaGL p k c hc0)⁻¹) = Matrix.ProjGenLinGroup.mk (B0 c hc) := by
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨(Units.mk0 (c ^ ((p - 1) / 2)) (pow_ne_zero _ hc0))⁻¹, ?_⟩
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
      deltaGL_coe, coe_GLmap, Matrix.GeneralLinearGroup.coe_scalar, B0_coe]
    rw [delta_conj_companion p k c hc0 hodd]
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      Fin.sum_univ_two, Units.val_inv_eq_inv_val, Units.val_mk0]
    fin_cases i <;> fin_cases j <;>
      simp [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ hc0)]
  have ht : (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) * tB0 p k c hc *
      (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k)))⁻¹ = tB0 p k c hc := by
    have hconj := Galois.fieldAut_conj_pgl (GaloisField p k) (frobEquiv p k) (B0 c hc)
    rw [alpha_coe, tB0]
    rw [show (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c hc0)) *
            galHom (GaloisField p k) (frobEquiv p k)) *
          pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (B0 c hc)) *
          (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c hc0)) *
            galHom (GaloisField p k) (frobEquiv p k))⁻¹
        = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c hc0)) *
          (galHom (GaloisField p k) (frobEquiv p k) *
            pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (B0 c hc)) *
            (galHom (GaloisField p k) (frobEquiv p k))⁻¹) *
          (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c hc0)))⁻¹ by
        group]
    rw [hconj]
    rw [show pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c hc0)) *
          pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map (frobEquiv p k) (B0 c hc))) *
          (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c hc0)))⁻¹
        = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (deltaGL p k c hc0 *
            Matrix.GeneralLinearGroup.map (frobEquiv p k) (B0 c hc) *
            (deltaGL p k c hc0)⁻¹)) by
        simp only [map_mul, map_inv]]
    rw [hkey]
  calc (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) * tB0 p k c hc
      = ((alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) * tB0 p k c hc *
          (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k)))⁻¹) *
          (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) := by group
    _ = tB0 p k c hc * (alpha p k c hc : Equiv.Perm (P1 (GaloisField p k))) := by rw [ht]


theorem torusConjPowB0 (hk : k ≠ 0) [DecidableEq (GaloisField p k)] (c : GaloisField p k)
    (hc : ¬ IsSquare c)
    (x : ↥(pgammaL (GaloisField p k)))
    (hx : (x : Equiv.Perm (P1 (GaloisField p k))) * tB0 p k c hc =
      tB0 p k c hc * (x : Equiv.Perm (P1 (GaloisField p k))))
    (i : ℕ) (hi : ∀ a : GaloisField p k, SplitAux.galMap (GaloisField p k) x a = a ^ (p ^ i)) :
    ∃ ε : ℤ, (ε = (p : ℤ) ^ i ∨ ε = -((p : ℤ) ^ i)) ∧
      ∀ u : TorUnits (GaloisField p k) c,
        (x : Equiv.Perm (P1 (GaloisField p k))) * torusPermB0 p k c hc u *
            (x : Equiv.Perm (P1 (GaloisField p k)))⁻¹ =
          torusPermB0 p k c hc (u ^ ε) := by
  have hodd : Odd p := odd_of_not_isSquare p k hk hc
  have hgalx : SplitAux.galMap (GaloisField p k) x = frobEquiv p k ^ i := by
    ext a
    rw [frobEquiv_pow_apply p k i a, hi a]
  set al : ↥(pgammaL (GaloisField p k)) := alpha p k c hc with hal
  set w : ↥(pgammaL (GaloisField p k)) := x * (al ^ i)⁻¹ with hw
  have hgalw : SplitAux.galMap (GaloisField p k) w = 1 := by
    rw [hw, map_mul, map_inv, map_pow, hgalx, hal, galMap_alpha p k c hc]
    rw [mul_inv_cancel]
  have hwpgl : (w : Equiv.Perm (P1 (GaloisField p k))) ∈ pglImage (GaloisField p k) :=
    (SplitAux.galPart_eq_one_iff (GaloisField p k) w).mp hgalw
  have hwcomm : Commute (w : Equiv.Perm (P1 (GaloisField p k))) (tB0 p k c hc) := by
    rw [hw]
    have hAcomm : Commute (al : Equiv.Perm (P1 (GaloisField p k))) (tB0 p k c hc) := by
      rw [hal]; exact alpha_comm_tB0 p k c hc hodd
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    have hxc : Commute (x : Equiv.Perm (P1 (GaloisField p k))) (tB0 p k c hc) := hx
    exact hxc.mul_left ((hAcomm.pow_left i).inv_left)
  obtain ⟨εw, hεw, hwact⟩ := wPartAux p k c hc hk w hwpgl hwcomm.eq
  refine ⟨εw * (p : ℤ) ^ i, ?_, ?_⟩
  · rcases hεw with h | h
    · left; rw [h, one_mul]
    · right; rw [h, neg_one_mul]
  · intro u
    have hxw : x = w * al ^ i := by rw [hw]; group
    have hkey : (x : Equiv.Perm (P1 (GaloisField p k))) * torusPermB0 p k c hc u *
          (x : Equiv.Perm (P1 (GaloisField p k)))⁻¹ =
        (w : Equiv.Perm (P1 (GaloisField p k))) * torusPermB0 p k c hc (u ^ p ^ i) *
          (w : Equiv.Perm (P1 (GaloisField p k)))⁻¹ := by
      rw [hxw]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      rw [show (w : Equiv.Perm (P1 (GaloisField p k))) * (al : Equiv.Perm (P1 (GaloisField p k))) ^ i *
            torusPermB0 p k c hc u *
            ((w : Equiv.Perm (P1 (GaloisField p k))) * (al : Equiv.Perm (P1 (GaloisField p k))) ^ i)⁻¹
          = (w : Equiv.Perm (P1 (GaloisField p k))) *
              ((al : Equiv.Perm (P1 (GaloisField p k))) ^ i * torusPermB0 p k c hc u *
                ((al : Equiv.Perm (P1 (GaloisField p k))) ^ i)⁻¹) *
              (w : Equiv.Perm (P1 (GaloisField p k)))⁻¹ by group]
      rw [← Subgroup.coe_pow, alpha_pow_torusPerm p k c hc hodd i u]
    rw [hkey, hwact (u ^ p ^ i)]
    congr 1
    rcases hεw with h | h
    · rw [h]
      rw [_root_.zpow_one, one_mul, ← Nat.cast_pow, _root_.zpow_natCast]
    · rw [h]
      rw [show (u ^ p ^ i) ^ (-1 : ℤ) = (u ^ p ^ i)⁻¹ from _root_.zpow_neg_one _,
        neg_one_mul, ← Nat.cast_pow, _root_.zpow_neg, _root_.zpow_natCast]


theorem torusConjPow (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) [DecidableEq (GaloisField p k)]
    (B : GL (Fin 2) (GaloisField p k)) (c : GaloisField p k)
    (hB : (B : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * B = c • 1)
    (hc : ¬ IsSquare c)
    (x : ↥(Work.AUTL2.pgammaL (GaloisField p k)))
    (hx : (x : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) *
            Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) =
          Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) *
            (x : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (i : ℕ) (hi : ∀ a : GaloisField p k,
      Work.DSTR.M110.SplitAux.galMap (GaloisField p k) x a = a ^ (p ^ i)) :
    ∃ ε : ℤ, (ε = (p : ℤ) ^ i ∨ ε = -((p : ℤ) ^ i)) ∧
      ∀ u : Work.DSTR.M110.TorUnits (GaloisField p k) c,
        (x : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * Work.DSTR.M110.torusPerm B c hB u *
            (x : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))⁻¹ =
          Work.DSTR.M110.torusPerm B c hB (u ^ ε) := by
  obtain ⟨S, hS⟩ := companionConjProof p k hk B c hB hc
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have hS' : (S : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
      (B : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
      (S : Matrix (Fin 2) (Fin 2) (GaloisField p k))⁻¹ =
      (B0 c hc : Matrix (Fin 2) (Fin 2) (GaloisField p k)) := by
    rw [hS, B0_coe]
  let s : ↥(pgammaL (GaloisField p k)) :=
    ⟨pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk S),
     pglImage_le_pgammaL _ (MonoidHom.mem_range.mpr ⟨Matrix.ProjGenLinGroup.mk S, rfl⟩)⟩
  have hsc : (s : Equiv.Perm (P1 (GaloisField p k))) =
      pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk S) := rfl
  have hs_pgl : (s : Equiv.Perm (P1 (GaloisField p k))) ∈ pglImage (GaloisField p k) :=
    MonoidHom.mem_range.mpr ⟨Matrix.ProjGenLinGroup.mk S, rfl⟩
  have hSB : S * B * S⁻¹ = B0 c hc := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv, hS']
  have htB0 : tB0 p k c hc = (s : Equiv.Perm (P1 (GaloisField p k))) *
      pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) *
      (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ := by
    have hAB : Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk B *
        (Matrix.ProjGenLinGroup.mk S)⁻¹ = Matrix.ProjGenLinGroup.mk (B0 c hc) := by
      rw [← map_mul, ← map_inv, ← map_mul, hSB]
    rw [tB0, hsc, ← hAB, map_mul, map_mul, map_inv]
  let x' : ↥(pgammaL (GaloisField p k)) := s * x * s⁻¹
  have hx' : (x' : Equiv.Perm (P1 (GaloisField p k))) * tB0 p k c hc =
      tB0 p k c hc * (x' : Equiv.Perm (P1 (GaloisField p k))) := by
    have hxc : (x' : Equiv.Perm (P1 (GaloisField p k))) =
        (s : Equiv.Perm (P1 (GaloisField p k))) * (x : Equiv.Perm (P1 (GaloisField p k))) *
          (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ := by
      simp only [x', Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hxc, htB0]
    rw [show (s : Equiv.Perm (P1 (GaloisField p k))) * (x : Equiv.Perm (P1 (GaloisField p k))) *
            (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ *
            ((s : Equiv.Perm (P1 (GaloisField p k))) *
              pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) *
              (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹)
        = (s : Equiv.Perm (P1 (GaloisField p k))) *
            ((x : Equiv.Perm (P1 (GaloisField p k))) * pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B)) *
            (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ by group]
    rw [show (s : Equiv.Perm (P1 (GaloisField p k))) * pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) *
            (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ *
            ((s : Equiv.Perm (P1 (GaloisField p k))) * (x : Equiv.Perm (P1 (GaloisField p k))) *
              (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹)
        = (s : Equiv.Perm (P1 (GaloisField p k))) *
            (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) * (x : Equiv.Perm (P1 (GaloisField p k)))) *
            (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ by group]
    rw [hx]
  have hi' : ∀ a : GaloisField p k,
      SplitAux.galMap (GaloisField p k) x' a = a ^ (p ^ i) := by
    intro a
    have hgal : SplitAux.galMap (GaloisField p k) x' = SplitAux.galMap (GaloisField p k) x := by
      rw [show x' = s * x * s⁻¹ from rfl]
      exact SplitAux.galMap_conj_mem_pglImage (GaloisField p k) s hs_pgl x
    rw [hgal, hi a]
  obtain ⟨ε, hε, hact⟩ := torusConjPowB0 p k hk c hc x' hx' i hi'
  refine ⟨ε, hε, ?_⟩
  intro u
  have hTPgen : ∀ v : TorUnits (GaloisField p k) c,
      torusPerm B c hB v = (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ *
        torusPermB0 p k c hc v * (s : Equiv.Perm (P1 (GaloisField p k))) := by
    intro v
    have hc_ := torusPermConjProof B (B0 c hc) c hB (B0_hB c hc) S hS' v
    rw [hsc.symm] at hc_
    rw [show torusPermB0 p k c hc v = torusPerm (B0 c hc) c (B0_hB c hc) v from rfl, hc_]
    group
  calc (x : Equiv.Perm (P1 (GaloisField p k))) * torusPerm B c hB u *
        (x : Equiv.Perm (P1 (GaloisField p k)))⁻¹
      = (x : Equiv.Perm (P1 (GaloisField p k))) *
          ((s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ * torusPermB0 p k c hc u *
            (s : Equiv.Perm (P1 (GaloisField p k)))) *
          (x : Equiv.Perm (P1 (GaloisField p k)))⁻¹ := by rw [hTPgen u]
    _ = (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ *
          ((x' : Equiv.Perm (P1 (GaloisField p k))) * torusPermB0 p k c hc u *
            (x' : Equiv.Perm (P1 (GaloisField p k)))⁻¹) *
          (s : Equiv.Perm (P1 (GaloisField p k))) := by
        rw [show (x' : Equiv.Perm (P1 (GaloisField p k))) =
            (s : Equiv.Perm (P1 (GaloisField p k))) * (x : Equiv.Perm (P1 (GaloisField p k))) *
              (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ by
          simp only [x', Subgroup.coe_mul, Subgroup.coe_inv]]
        group
    _ = (s : Equiv.Perm (P1 (GaloisField p k)))⁻¹ * torusPermB0 p k c hc (u ^ ε) *
          (s : Equiv.Perm (P1 (GaloisField p k))) := by rw [hact u]
    _ = torusPerm B c hB (u ^ ε) := by rw [hTPgen (u ^ ε)]

end Work.DSTR.M110
