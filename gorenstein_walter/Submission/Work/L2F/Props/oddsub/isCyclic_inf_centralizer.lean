import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Props.oddsub.exists_smul_one_add_smul_of_commute
import Submission.Work.L2F.Props.oddsub.smul_one_add_smul_eq_zero
import Submission.Work.L2F.Props.oddsub.eval_mul_coeff
import Submission.Work.L2F.Props.oddsub.eq_one_of_eval_eq_one
import Submission.Work.L2F.Props.oddsub.ne_of_add_eq_trace_mul_eq_det

/-!
# The centralizer of a semisimple element of `SL(2,F)`

For a field `F`, a finite subgroup `G ≤ SL(2,F)` and an element `t ∈ SL(2,F)` whose
characteristic polynomial is separable (`SemisimpleSL t`, i.e. `t` has two distinct eigenvalues
over an algebraic closure), the subgroup `G ⊓ C_{SL(2,F)}(t)` is cyclic.

Proof.  Every `h` commuting with `t` is a polynomial in `t`: `h = a • 1 + b • t`
(`exists_smul_one_add_smul_of_commute`), with unique coefficients
(`smul_one_add_smul_eq_zero`).  Pick a root `λ` of `X² - tr(t)·X + det(t)` in the algebraic
closure `L = F̄`; then `λ` and `μ = tr(t) - λ` are the two *distinct* roots of the characteristic
polynomial (`ne_of_add_eq_trace_mul_eq_det`).  The map

  `h = a • 1 + b • t ↦ a + b·λ`

is a multiplicative map from `C_{SL(2,F)}(t)` into the field `L`: multiplicativity of the
coefficients is `eval_mul_coeff`, and — using `det h = 1` — it is injective on `SL(2,F)`
(`eq_one_of_eval_eq_one`).  A finite subgroup of the units of an integral domain is cyclic
(`isCyclic_of_injective_ringHom`).
-/

noncomputable section

open Matrix

namespace Work.L2F.Props.oddsub

variable {F : Type*} [Field F]

/-! ## The centralizer of `t` and its coefficient map -/

/-- The centralizer in `SL(2,F)` of a single element. -/
abbrev Ct (t : Matrix.SpecialLinearGroup (Fin 2) F) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
  Subgroup.centralizer ({t} : Set (Matrix.SpecialLinearGroup (Fin 2) F))

/-- An element of the centralizer of `x` commutes with `x` as a matrix. -/
lemma commute_of_mem_centralizer {x y : Matrix.SpecialLinearGroup (Fin 2) F} (h : y ∈ Ct x) :
    (y : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
      = (x : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) := by
  have h' := Subgroup.mem_centralizer_singleton_iff.mp h
  simpa using congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
    (z : Matrix (Fin 2) (Fin 2) F)) h'

/-- The coefficient map of the existence statement, at the level of a single group element. -/
private def coeffsOf (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : ∀ c : F, (t : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (h : ↥(Ct t)) : F × F :=
  let h' := exists_smul_one_add_smul_of_commute F (t : Matrix (Fin 2) (Fin 2) F)
    ((h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ht
    (commute_of_mem_centralizer h.2)
  (Classical.choose h', Classical.choose (Classical.choose_spec h'))

private lemma coeffsOf_spec (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : ∀ c : F, (t : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (h : ↥(Ct t)) :
    ((h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = (coeffsOf t ht h).1 • (1 : Matrix (Fin 2) (Fin 2) F)
        + (coeffsOf t ht h).2 • (t : Matrix (Fin 2) (Fin 2) F) := by
  have h' := exists_smul_one_add_smul_of_commute F (t : Matrix (Fin 2) (Fin 2) F)
    ((h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ht
    (commute_of_mem_centralizer h.2)
  exact Classical.choose_spec (Classical.choose_spec h')

/-- The coefficients in `x • 1 + y • t` are unique when `t` is not a scalar matrix. -/
lemma coeff_eq_of_eq (t : Matrix (Fin 2) (Fin 2) F)
    (ht : ∀ c : F, t ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    {x y x' y' : F}
    (h : x • (1 : Matrix (Fin 2) (Fin 2) F) + y • t
      = x' • (1 : Matrix (Fin 2) (Fin 2) F) + y' • t) : x = x' ∧ y = y' := by
  have h0 : (x - x') • (1 : Matrix (Fin 2) (Fin 2) F) + (y - y') • t = 0 := by
    have h' : (x - x') • (1 : Matrix (Fin 2) (Fin 2) F) + (y - y') • t
        = (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • t)
          - (x' • (1 : Matrix (Fin 2) (Fin 2) F) + y' • t) := by
      rw [sub_smul, sub_smul]
      abel
    rw [h', h, sub_self]
  obtain ⟨h1, h2⟩ := smul_one_add_smul_eq_zero F t ht (x - x') (y - y') h0
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-- The "eigenvalue" of `h ∈ C(t)` on the eigenspace of `t` for the root `lam`, computed from
the coefficients of `h` in the basis `(1, t)`. -/
def evalFun (L : Type*) [Field L] [Algebra F L] (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : ∀ c : F, (t : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (lam : L) (h : ↥(Ct t)) : L :=
  algebraMap F L (coeffsOf t ht h).1 + algebraMap F L (coeffsOf t ht h).2 * lam

lemma evalFun_one (L : Type*) [Field L] [Algebra F L] (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : ∀ c : F, (t : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (lam : L) : evalFun L t ht lam 1 = 1 := by
  have h1 := coeffsOf_spec t ht (1 : ↥(Ct t))
  obtain ⟨ha, hb⟩ := coeff_eq_of_eq (t := (t : Matrix (Fin 2) (Fin 2) F)) ht
    (x := (coeffsOf t ht 1).1) (y := (coeffsOf t ht 1).2) (x' := 1) (y' := 0) (by
      rw [← h1]
      simp)
  simp only [evalFun, ha, hb, map_one, map_zero, zero_mul, add_zero]

lemma evalFun_mul (L : Type*) [Field L] [Algebra F L] (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : ∀ c : F, (t : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (lam : L)
    (hlam : lam ^ 2 = algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).trace * lam
      - algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).det)
    (h1 h2 : ↥(Ct t)) :
    evalFun L t ht lam (h1 * h2) = evalFun L t ht lam h1 * evalFun L t ht lam h2 := by
  obtain ⟨hmul, heval⟩ := eval_mul_coeff F L (t : Matrix (Fin 2) (Fin 2) F) lam hlam
    (coeffsOf t ht h1).1 (coeffsOf t ht h1).2 (coeffsOf t ht h2).1 (coeffsOf t ht h2).2
  have hs1 := coeffsOf_spec t ht h1
  have hs2 := coeffsOf_spec t ht h2
  have hs12 := coeffsOf_spec t ht (h1 * h2)
  have hcoe : (((h1 * h2 : ↥(Ct t)) : Matrix.SpecialLinearGroup (Fin 2) F)
        : Matrix (Fin 2) (Fin 2) F)
      = ((h1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        * ((h2 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hprod : (((h1 * h2 : ↥(Ct t)) : Matrix.SpecialLinearGroup (Fin 2) F)
        : Matrix (Fin 2) (Fin 2) F)
      = ((coeffsOf t ht h1).1 * (coeffsOf t ht h2).1
          - (coeffsOf t ht h1).2 * (coeffsOf t ht h2).2 * (t : Matrix (Fin 2) (Fin 2) F).det) • 1
        + ((coeffsOf t ht h1).1 * (coeffsOf t ht h2).2
            + (coeffsOf t ht h1).2 * (coeffsOf t ht h2).1
            + (coeffsOf t ht h1).2 * (coeffsOf t ht h2).2
              * (t : Matrix (Fin 2) (Fin 2) F).trace) • (t : Matrix (Fin 2) (Fin 2) F) := by
    rw [hcoe, hs1, hs2]
    exact hmul
  have key : (coeffsOf t ht (h1 * h2)).1
        = (coeffsOf t ht h1).1 * (coeffsOf t ht h2).1
          - (coeffsOf t ht h1).2 * (coeffsOf t ht h2).2 * ((t : Matrix (Fin 2) (Fin 2) F)).det
      ∧ (coeffsOf t ht (h1 * h2)).2
        = (coeffsOf t ht h1).1 * (coeffsOf t ht h2).2
          + (coeffsOf t ht h1).2 * (coeffsOf t ht h2).1
          + (coeffsOf t ht h1).2 * (coeffsOf t ht h2).2 * ((t : Matrix (Fin 2) (Fin 2) F)).trace := by
    refine coeff_eq_of_eq (t := (t : Matrix (Fin 2) (Fin 2) F)) ht ?_
    rw [← hs12, hprod]
  simp only [evalFun, key.1, key.2]
  rw [← heval]

/-- The coefficient map is a monoid homomorphism `C_{SL(2,F)}(t) →* L`. -/
def evalHom (L : Type*) [Field L] [Algebra F L] (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : ∀ c : F, (t : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (lam : L)
    (hlam : lam ^ 2 = algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).trace * lam
      - algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).det) :
    ↥(Ct t) →* L where
  toFun := evalFun L t ht lam
  map_one' := evalFun_one L t ht lam
  map_mul' := evalFun_mul L t ht lam hlam

/-- If `evalFun h = 1` for `h ∈ C(t) ⊆ SL(2,F)` then `h = 1`; this is the injectivity of the
coefficient map on the determinant-one part. -/
lemma evalFun_eq_one_imp (L : Type*) [Field L] [Algebra F L]
    (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : ∀ c : F, (t : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (lam : L) (mu : L)
    (hsum : lam + mu = algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).trace)
    (hprod : lam * mu = algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).det)
    (hne : lam ≠ mu) (h : ↥(Ct t)) (hone : evalFun L t ht lam h = 1) : h = 1 := by
  have hsp := coeffsOf_spec t ht h
  have hdet : ((coeffsOf t ht h).1 • (1 : Matrix (Fin 2) (Fin 2) F)
      + (coeffsOf t ht h).2 • (t : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
    rw [← hsp]
    exact Matrix.SpecialLinearGroup.det_coe (h : Matrix.SpecialLinearGroup (Fin 2) F)
  obtain ⟨ha, hb⟩ := eq_one_of_eval_eq_one F L (t : Matrix (Fin 2) (Fin 2) F) lam mu hsum hprod
    hne (coeffsOf t ht h).1 (coeffsOf t ht h).2 hone hdet
  have hmat : ((h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [hsp, ha, hb]
    simp
  exact Subtype.ext (Subtype.ext hmat)

lemma evalHom_injective (L : Type*) [Field L] [Algebra F L]
    (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : ∀ c : F, (t : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (lam : L)
    (hlam : lam ^ 2 = algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).trace * lam
      - algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).det)
    (mu : L)
    (hsum : lam + mu = algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).trace)
    (hprod : lam * mu = algebraMap F L (t : Matrix (Fin 2) (Fin 2) F).det)
    (hne : lam ≠ mu) : Function.Injective (evalHom L t ht lam hlam) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  exact evalFun_eq_one_imp L t ht lam mu hsum hprod hne x (MonoidHom.mem_ker.mp hx)

/-! ## The main theorem -/

theorem isCyclic_inf_centralizer (F : Type*) [Field F]
    (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [Finite G]
    (t : Matrix.SpecialLinearGroup (Fin 2) F)
    (ht : Work.L2F.Props.SemisimpleSL (t : Matrix (Fin 2) (Fin 2) F)) :
    IsCyclic ↥(G ⊓ Subgroup.centralizer ({t} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  classical
  haveI : Finite ↥(G ⊓ Subgroup.centralizer ({t} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    Finite.of_injective
      (fun x : ↥(G ⊓ Subgroup.centralizer ({t} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) =>
        (⟨(x : Matrix.SpecialLinearGroup (Fin 2) F), x.2.1⟩ : ↥G))
      (fun x y h => by
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext h)
  -- a root of the characteristic polynomial in an algebraic closure
  obtain ⟨lam, hlamroot⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 - Polynomial.C (algebraMap F (AlgebraicClosure F)
        ((t : Matrix (Fin 2) (Fin 2) F)).trace) * Polynomial.X
      + Polynomial.C (algebraMap F (AlgebraicClosure F) ((t : Matrix (Fin 2) (Fin 2) F)).det))
    (by
      rw [show (Polynomial.X ^ 2 - Polynomial.C (algebraMap F (AlgebraicClosure F)
            ((t : Matrix (Fin 2) (Fin 2) F)).trace) * Polynomial.X
          + Polynomial.C (algebraMap F (AlgebraicClosure F)
            ((t : Matrix (Fin 2) (Fin 2) F)).det) : Polynomial (AlgebraicClosure F)).degree = 2 from by
        compute_degree!]
      norm_num)
  have hlam : lam ^ 2 = algebraMap F (AlgebraicClosure F) ((t : Matrix (Fin 2) (Fin 2) F)).trace * lam
      - algebraMap F (AlgebraicClosure F) ((t : Matrix (Fin 2) (Fin 2) F)).det := by
    rw [Polynomial.IsRoot.def] at hlamroot
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hlamroot
    linear_combination hlamroot
  set mu : AlgebraicClosure F :=
    algebraMap F (AlgebraicClosure F) ((t : Matrix (Fin 2) (Fin 2) F)).trace - lam with hmu
  have hsum : lam + mu
      = algebraMap F (AlgebraicClosure F) ((t : Matrix (Fin 2) (Fin 2) F)).trace := by
    rw [hmu]; ring
  have hprod : lam * mu
      = algebraMap F (AlgebraicClosure F) ((t : Matrix (Fin 2) (Fin 2) F)).det := by
    rw [hmu]
    linear_combination -hlam
  have hne : lam ≠ mu := ne_of_add_eq_trace_mul_eq_det F (AlgebraicClosure F)
    ((t : Matrix (Fin 2) (Fin 2) F)).trace ((t : Matrix (Fin 2) (Fin 2) F)).det lam mu hsum hprod ht.2
  refine isCyclic_of_injective_ringHom
    ((evalHom (AlgebraicClosure F) t ht.1 lam hlam).comp
      (Subgroup.inclusion (inf_le_right : G ⊓ Ct t ≤ Ct t))) ?_
  exact (evalHom_injective (AlgebraicClosure F) t ht.1 lam hlam mu hsum hprod hne).comp
    (Subgroup.inclusion_injective _)

end Work.L2F.Props.oddsub
