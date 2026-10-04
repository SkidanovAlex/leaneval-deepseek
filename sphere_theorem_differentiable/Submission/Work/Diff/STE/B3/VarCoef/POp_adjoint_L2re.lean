import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarDef
import Submission.Work.Diff.STE.B3.VarCoef.Assembly
import Submission.Work.Diff.STE.B3.VarCoef.VarCoefAssembly
import Submission.Work.Diff.STE.B3.VarCoef.pdAux
import Submission.Work.Diff.STE.B3.VarCoef.varLapDiffDefs
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.cm_pd_L2re_adjoint
import Submission.Work.Diff.STE.B3.VarCoef.cm_pd_pd_L2re_adjoint
import Submission.Work.Diff.STE.B3.VarCoef.varLapOp_preserves
import Submission.Work.Diff.STE.B3.SymCalcStep7.pairSharpAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `L²`-adjointness of `POp c c' (varLap A B) k`

The target of this file is the formal adjointness of the composite operator
`POp c c' (varLapOp A B) k = M_{c'} ∘ D^k ∘ M_c` (`D = varLap A B`) for the flat pairing
`L2re f g = Re ∫_{unitCube} f · conj g` of the torus:

  `L2re (POp c c' D k p) q = L2re p (POpStar c c' A (-B) k q)`,

where `POpStar c c' A B k = M_c ∘ E^k ∘ M_{c'}` and `E = varLapStar A B` is the formal adjoint of
`D = varLap A B` (`varLapStarDef.lean`).  All coefficients are real-valued, so all the
conjugations that appear are pointwise (`pdAux.lean`).

## The structure of the proof

1. `L2re` is additive over finite sums in each argument (`L2re_finset_sum_fst/snd`), so the two
   defining sums of `varLap` and `varLapStar` (`varLap_eq_sum`, `varLapStar_eq_sum`) distribute
   over the pairing (`L2re_varLap_decomp`, `L2re_varLapStar_decomp`).
2. The single terms are matched by the two integration-by-parts identities
   `cm_pd_pd_L2re_adjoint` (`L2re (m ∂_a∂_b f) g = L2re f (∂_a∂_b (m g))`) and
   `cm_pd_L2re_adjoint` (`L2re (m ∂_a f) g = - L2re f (∂_a (m g))`), which are proved in the
   sibling modules and are the mathematical content of the computation.  Together they give the
   **single step** `varLap_L2re_adjoint`:
   `L2re (varLap A B f) g = L2re f (varLapStar A (-B) g)`.
3. `varLap A B` and `varLapStar A B` preserve smooth `1`-periodic functions
   (`varLapOp_preserves`, `varLapStarOp_preserves`), so the single step iterates to the `k`-th
   powers (`varLapPow_L2re_adjoint`).
4. Multiplication by a real coefficient is self-adjoint (`mulOp_L2re_adjoint`), and the outer
   multipliers `c`, `c'` are moved across the pairing, which is exactly the shape of `POpStar`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

open Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Elementary linearity of `L2re` -/

/-- A finite sum of continuous functions is continuous. -/
theorem continuous_finset_sum_fun {κ : Type*} (S : Finset κ) (F : κ → (ι → ℝ) → ℂ)
    (h : ∀ i ∈ S, Continuous (F i)) : Continuous (fun x => ∑ i ∈ S, F i x) :=
  continuous_finsetSum S h

/-- Additivity of `L2re` over a finite sum in its **first** argument. -/
theorem L2re_finset_sum_fst {κ : Type*} (S : Finset κ) (F : κ → (ι → ℝ) → ℂ)
    (g : (ι → ℝ) → ℂ) (hF : ∀ i ∈ S, Continuous (F i)) (hg : Continuous g) :
    L2re (fun x => ∑ i ∈ S, F i x) g = ∑ i ∈ S, L2re (F i) g := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      simp only [Work.Diff.STE.L2re]
      simp
  | insert a S ha ih =>
      have hFa : Continuous (F a) := hF a (Finset.mem_insert_self a S)
      have hFS : ∀ i ∈ S, Continuous (F i) := fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsum : Continuous (fun x : ι → ℝ => ∑ i ∈ S, F i x) := continuous_finsetSum S hFS
      have hsplit : (fun x : ι → ℝ => ∑ i ∈ insert a S, F i x)
          = F a + fun x : ι → ℝ => ∑ i ∈ S, F i x := by
        funext x
        simp only [Pi.add_apply, Finset.sum_insert ha]
      rw [hsplit, Finset.sum_insert ha,
        Work.Diff.STE.B3.SymCalcStep7.L2re_add_fst' hFa hsum hg, ih hFS]

/-- Additivity of `L2re` over a finite sum in its **second** argument. -/
theorem L2re_finset_sum_snd {κ : Type*} (S : Finset κ) (F : κ → (ι → ℝ) → ℂ)
    (f : (ι → ℝ) → ℂ) (hF : ∀ i ∈ S, Continuous (F i)) (hf : Continuous f) :
    L2re f (fun x => ∑ i ∈ S, F i x) = ∑ i ∈ S, L2re f (F i) := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      simp only [Work.Diff.STE.L2re]
      simp
  | insert a S ha ih =>
      have hFa : Continuous (F a) := hF a (Finset.mem_insert_self a S)
      have hFS : ∀ i ∈ S, Continuous (F i) := fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsum : Continuous (fun x : ι → ℝ => ∑ i ∈ S, F i x) := continuous_finsetSum S hFS
      have hsplit : (fun x : ι → ℝ => ∑ i ∈ insert a S, F i x)
          = F a + fun x : ι → ℝ => ∑ i ∈ S, F i x := by
        funext x
        simp only [Pi.add_apply, Finset.sum_insert ha]
      rw [hsplit, Finset.sum_insert ha,
        Work.Diff.STE.B3.SymCalcStep7.L2re_add_snd' hf hFa hsum, ih hFS]

/-- Negation in the first argument of `L2re`, in the `Pi.neg` shape. -/
theorem L2re_neg_fst' (y g : (ι → ℝ) → ℂ) : L2re (-y) g = -L2re y g :=
  Work.Diff.STE.B3.SymCalcStep7.L2re_neg_fst y g

/-- Negation in the second argument of `L2re`, in the `Pi.neg` shape. -/
theorem L2re_neg_snd' (y g : (ι → ℝ) → ℂ) : L2re y (-g) = -L2re y g :=
  Work.Diff.STE.B3.SymCalcStep7.L2re_neg_snd y g

/-! ## 2. The two defining sums of `varLap` and `varLapStar` -/

/-- The pointwise sum decomposition of `varLap`. -/
theorem varLap_eq_sum (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (f : (ι → ℝ) → ℂ) :
    varLap A B f = fun x => -((∑ a, ∑ b, ((A a b x : ℝ) : ℂ) * pd a (pd b f) x)
        + ∑ a, ((B a x : ℝ) : ℂ) * pd a f x) := by
  funext x
  simp only [varLap, Finset.sum_apply, Pi.add_apply, Pi.neg_apply]

/-- The pointwise sum decomposition of `varLapStar`. -/
theorem varLapStar_eq_sum (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (g : (ι → ℝ) → ℂ) :
    varLapStar A B g
      = fun x => -((∑ a, ∑ b, pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)) x)
          + ∑ a, pd a (fun x => ((B a x : ℝ) : ℂ) * g x) x) := by
  funext x
  simp only [varLapStar, Finset.sum_apply, Pi.add_apply, Pi.neg_apply]

/-- `pd` commutes with the pointwise negation of a function. -/
theorem pd_neg' (a : ι) (h : (ι → ℝ) → ℂ) : pd a (-h) = -pd a h := by
  funext x
  show (fderiv ℝ (-h) x) (Pi.single a 1) = -((fderiv ℝ h x) (Pi.single a 1))
  rw [fderiv_neg]
  rfl

/-- Negation preserves `1`-periodicity. -/
theorem periodic1_neg' {β : Type*} [Neg β] {f : (ι → ℝ) → β} (hf : Periodic1 f) :
    Periodic1 (-f) := fun i x => by simp only [Pi.neg_apply, hf i x]

/-- The negation of a family of smooth real functions is smooth termwise. -/
theorem contDiff_neg_fun {B : ι → (ι → ℝ) → ℝ} (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) :
    ∀ a, ContDiff ℝ (⊤ : ℕ∞) ((fun a => -B a) a) := fun a => (hB a).neg

/-- The negation of a family of `1`-periodic real functions is `1`-periodic termwise. -/
theorem periodic1_neg_fun {B : ι → (ι → ℝ) → ℝ} (hB : ∀ a, Periodic1 (B a)) :
    ∀ a, Periodic1 ((fun a => -B a) a) := fun a => periodic1_neg' (hB a)

/-! ## 3. Preservation of smooth `1`-periodic functions -/

/-- `varLapStar A B` preserves smooth `1`-periodic functions. -/
theorem varLapStar_smoothPer (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Periodic1 (B a))
    {g : (ι → ℝ) → ℂ} (hg : SmoothPer g) : SmoothPer (varLapStar A B g) := by
  constructor
  · rw [varLapStar_eq_sum]
    exact ContDiff.neg (ContDiff.add
      (ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
        pd_contDiff_top (pd_contDiff_top
          ((Complex.ofRealCLM.contDiff.comp (hA a b)).mul hg.1) b) a)))
      (ContDiff.sum (fun a _ =>
        pd_contDiff_top ((Complex.ofRealCLM.contDiff.comp (hB a)).mul hg.1) a)))
  · intro i x
    show (varLapStar A B g) (x + Pi.single i 1) = (varLapStar A B g) x
    rw [varLapStar_eq_sum]
    simp only [Pi.neg_apply, Pi.add_apply]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [pd_periodic1 (pd_periodic1 (fun i' y => by
          simp only [hAp a b i' y, hg.2 i' y]) b) a i x]
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [pd_periodic1 (fun i' y => by
          simp only [hBp a i' y, hg.2 i' y]) a i x]

/-- `varLapStar A B` preserves smooth `1`-periodic functions (operator form). -/
theorem varLapStarOp_preserves (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Periodic1 (B a)) :
    Preserves (varLapStarOp A B) :=
  fun g hg => varLapStar_smoothPer A B hA hAp hB hBp hg

/-- A multiplier preserves smooth `1`-periodic functions. -/
theorem SmoothPer.mulOp' {m : (ι → ℝ) → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hmp : Periodic1 m) {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) :
    SmoothPer (mulOp m f) := by
  refine ⟨?_, ?_⟩
  · show ContDiff ℝ (⊤ : ℕ∞) (fun x => ((m x : ℝ) : ℂ) * f x)
    exact (Complex.ofRealCLM.contDiff.comp hm).mul hf.1
  · intro i x
    show ((m (x + Pi.single i 1) : ℝ) : ℂ) * f (x + Pi.single i 1)
        = ((m x : ℝ) : ℂ) * f x
    rw [hmp i x, hf.2 i x]

/-! ## 4. The `L2re` decompositions of `varLap` and `varLapStar` -/

/-- Distribution of `L2re (varLap A B f) g` over the defining sums. -/
theorem L2re_varLap_decomp (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Periodic1 (B a))
    (f g : (ι → ℝ) → ℂ) (hf : SmoothPer f) (hg : SmoothPer g) :
    L2re (varLap A B f) g
      = -((∑ a, ∑ b, L2re (fun x => ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) g)
          + ∑ a, L2re (fun x => ((B a x : ℝ) : ℂ) * pd a f x) g) := by
  have h1 : ∀ a b, Continuous (fun x : ι → ℝ => ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) :=
    fun a b => ((Complex.ofRealCLM.contDiff.comp (hA a b)).continuous).mul
      ((pd_contDiff_top (pd_contDiff_top hf.1 b) a).continuous)
  have h2 : ∀ a, Continuous (fun x : ι → ℝ => ((B a x : ℝ) : ℂ) * pd a f x) :=
    fun a => ((Complex.ofRealCLM.contDiff.comp (hB a)).continuous).mul
      ((pd_contDiff_top hf.1 a).continuous)
  have hcu1 : Continuous (fun x : ι → ℝ => ∑ a, ∑ b,
      ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) :=
    continuous_finset_sum_fun Finset.univ
      (fun a => fun x => ∑ b, ((A a b x : ℝ) : ℂ) * pd a (pd b f) x)
      (fun a _ => continuous_finset_sum_fun Finset.univ
        (fun b => fun x => ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) (fun b _ => h1 a b))
  have hcu2 : Continuous (fun x : ι → ℝ => ∑ a, ((B a x : ℝ) : ℂ) * pd a f x) :=
    continuous_finset_sum_fun Finset.univ
      (fun a => fun x => ((B a x : ℝ) : ℂ) * pd a f x) (fun a _ => h2 a)
  have hvar : varLap A B f
      = -((fun x : ι → ℝ => ∑ a, ∑ b, ((A a b x : ℝ) : ℂ) * pd a (pd b f) x)
          + (fun x : ι → ℝ => ∑ a, ((B a x : ℝ) : ℂ) * pd a f x)) := by
    rw [varLap_eq_sum]
    rfl
  have hsum1 : L2re (fun x : ι → ℝ => ∑ a, ∑ b,
        ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) g
      = ∑ a, ∑ b, L2re (fun x => ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) g := by
    rw [L2re_finset_sum_fst Finset.univ
      (fun a => fun x => ∑ b, ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) g
      (fun a _ => continuous_finset_sum_fun Finset.univ
        (fun b => fun x => ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) (fun b _ => h1 a b))
      hg.continuous]
    exact Finset.sum_congr rfl fun a _ => L2re_finset_sum_fst Finset.univ
      (fun b => fun x => ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) g (fun b _ => h1 a b)
      hg.continuous
  have hsum2 : L2re (fun x : ι → ℝ => ∑ a, ((B a x : ℝ) : ℂ) * pd a f x) g
      = ∑ a, L2re (fun x => ((B a x : ℝ) : ℂ) * pd a f x) g :=
    L2re_finset_sum_fst Finset.univ (fun a => fun x => ((B a x : ℝ) : ℂ) * pd a f x) g
      (fun a _ => h2 a) hg.continuous
  rw [hvar, L2re_neg_fst',
    Work.Diff.STE.B3.SymCalcStep7.L2re_add_fst' hcu1 hcu2 hg.continuous, hsum1, hsum2]

/-- Distribution of `L2re h (varLapStar A B g)` over the defining sums. -/
theorem L2re_varLapStar_decomp (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Periodic1 (B a))
    (g h : (ι → ℝ) → ℂ) (hg : SmoothPer g) (hh : SmoothPer h) :
    L2re h (varLapStar A B g)
      = -((∑ a, ∑ b, L2re h (pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x))))
          + ∑ a, L2re h (pd a (fun x => ((B a x : ℝ) : ℂ) * g x))) := by
  have h1 : ∀ a b, Continuous
      (pd a (pd b (fun x : ι → ℝ => ((A a b x : ℝ) : ℂ) * g x))) :=
    fun a b => (pd_contDiff_top (pd_contDiff_top
      ((Complex.ofRealCLM.contDiff.comp (hA a b)).mul hg.1) b) a).continuous
  have h2 : ∀ a, Continuous (pd a (fun x : ι → ℝ => ((B a x : ℝ) : ℂ) * g x)) :=
    fun a => (pd_contDiff_top ((Complex.ofRealCLM.contDiff.comp (hB a)).mul hg.1) a).continuous
  have hcu1 : Continuous (fun x : ι → ℝ => ∑ a, ∑ b,
      pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)) x) :=
    continuous_finset_sum_fun Finset.univ
      (fun a => fun x => ∑ b, pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)) x)
      (fun a _ => continuous_finset_sum_fun Finset.univ
        (fun b => fun x => pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)) x)
        (fun b _ => h1 a b))
  have hcu2 : Continuous (fun x : ι → ℝ => ∑ a,
      pd a (fun x => ((B a x : ℝ) : ℂ) * g x) x) :=
    continuous_finset_sum_fun Finset.univ
      (fun a => fun x => pd a (fun x => ((B a x : ℝ) : ℂ) * g x) x) (fun a _ => h2 a)
  have hstar : varLapStar A B g
      = -((fun x : ι → ℝ => ∑ a, ∑ b, pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)) x)
          + (fun x : ι → ℝ => ∑ a, pd a (fun x => ((B a x : ℝ) : ℂ) * g x) x)) := by
    rw [varLapStar_eq_sum]
    rfl
  have hsum1 : L2re h (fun x : ι → ℝ => ∑ a, ∑ b,
        pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)) x)
      = ∑ a, ∑ b, L2re h (pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x))) := by
    rw [L2re_finset_sum_snd Finset.univ
      (fun a => fun x => ∑ b, pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)) x) h
      (fun a _ => continuous_finset_sum_fun Finset.univ
        (fun b => fun x => pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)) x)
        (fun b _ => h1 a b)) hh.continuous]
    exact Finset.sum_congr rfl fun a _ => L2re_finset_sum_snd Finset.univ
      (fun b => fun x => pd a (pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)) x) h
      (fun b _ => h1 a b) hh.continuous
  have hsum2 : L2re h (fun x : ι → ℝ => ∑ a,
        pd a (fun x => ((B a x : ℝ) : ℂ) * g x) x)
      = ∑ a, L2re h (pd a (fun x => ((B a x : ℝ) : ℂ) * g x)) :=
    L2re_finset_sum_snd Finset.univ
      (fun a => fun x => pd a (fun x => ((B a x : ℝ) : ℂ) * g x) x) h (fun a _ => h2 a)
      hh.continuous
  rw [hstar, L2re_neg_snd',
    Work.Diff.STE.B3.SymCalcStep7.L2re_add_snd' hh.continuous hcu1 hcu2, hsum1, hsum2]

/-! ## 5. The single step: `varLap A B` against `varLapStar A (-B)` -/

/-- **The single-step adjointness.**  `varLapStar A (-B)` is the `L2re`-adjoint of `varLap A B`. -/
theorem varLap_L2re_adjoint (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Periodic1 (B a))
    {f g : (ι → ℝ) → ℂ} (hf : SmoothPer f) (hg : SmoothPer g) :
    L2re (varLap A B f) g = L2re f (varLapStar A (fun a => -B a) g) := by
  rw [L2re_varLap_decomp A B hA hAp hB hBp f g hf hg,
    L2re_varLapStar_decomp A (fun a => -B a) hA hAp (contDiff_neg_fun hB) (periodic1_neg_fun hBp)
      g f hg hf]
  have h1 : (∑ a, ∑ b, L2re (fun x : ι → ℝ => ((A a b x : ℝ) : ℂ) * pd a (pd b f) x) g)
      = ∑ a, ∑ b, L2re f (pd a (pd b (fun y : ι → ℝ => ((A a b y : ℝ) : ℂ) * g y))) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      cm_pd_pd_L2re_adjoint (A a b) a b f g (hA a b) (hAp a b) hf.1 hf.2 hg.1 hg.2
  have h2 : (∑ a, L2re (fun x : ι → ℝ => ((B a x : ℝ) : ℂ) * pd a f x) g)
      = ∑ a, L2re f (pd a (fun y : ι → ℝ => ((-(B a y) : ℝ) : ℂ) * g y)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [cm_pd_L2re_adjoint (B a) a f g (hB a) (hBp a) hf.1 hf.2 hg.1 hg.2]
    rw [show (fun y : ι → ℝ => ((-(B a y) : ℝ) : ℂ) * g y)
          = -(fun y : ι → ℝ => ((B a y : ℝ) : ℂ) * g y) from by
        funext y
        simp only [Pi.neg_apply, Complex.ofReal_neg, neg_mul],
      pd_neg', L2re_neg_snd']
  rw [h1, h2]
  simp only [Pi.neg_apply]

/-! ## 6. The `k`-th powers -/

/-- The `k`-fold iterate of a `SmoothPer`-preserving operator preserves `SmoothPer`. -/
theorem iterate_smoothPer {D : Op ι} (hD : Preserves D) (k : ℕ) {f : (ι → ℝ) → ℂ}
    (hf : SmoothPer f) : SmoothPer ((D^[k]) f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact hD _ ih

/-- **The `k`-th power adjointness.** -/
theorem varLapPow_L2re_adjoint (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Periodic1 (B a)) :
    ∀ (k : ℕ) (f g : (ι → ℝ) → ℂ), SmoothPer f → SmoothPer g →
      L2re (((varLapOp A B)^[k]) f) g
        = L2re f (((varLapStarOp A (fun a => -B a))^[k]) g) := by
  intro k
  induction k with
  | zero => intro f g hf hg; simp
  | succ k ih =>
      intro f g hf hg
      have hD : Preserves (varLapOp A B) := varLapOp_preserves A B hA hAp hB hBp
      have hE : Preserves (varLapStarOp A (fun a => -B a)) :=
        varLapStarOp_preserves A (fun a => -B a) hA hAp
          (contDiff_neg_fun hB) (periodic1_neg_fun hBp)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply]
      change L2re (varLap A B (((varLapOp A B)^[k]) f)) g
        = L2re f (((varLapStar A (fun a => -B a))^[k]) (varLapStar A (fun a => -B a) g))
      rw [varLap_L2re_adjoint A B hA hAp hB hBp (iterate_smoothPer hD k hf) hg]
      exact ih f (varLapStar A (fun a => -B a) g) hf (hE g hg)

/-! ## 7. Multipliers and the assembly -/

/-- Multiplication by a real coefficient is self-adjoint for `L2re`. -/
theorem mulOp_L2re_adjoint (c : (ι → ℝ) → ℝ) (u v : (ι → ℝ) → ℂ) :
    L2re (mulOp c u) v = L2re u (mulOp c v) := by
  rw [show mulOp c u = fun x : ι → ℝ => ((c x : ℝ) : ℂ) * u x from rfl]
  rw [Work.Diff.STE.B3.SymCalcStep7.L2re_mul_fst]
  rw [show (fun x : ι → ℝ => star (((c x : ℝ) : ℂ)) * v x) = mulOp c v from by
    funext x
    simp only [mulOp]
    rw [star_cm]]

/-- The assembled adjointness of `POp c c' (varLapOp A B) k`. -/
theorem POp_L2re_adjoint (c c' : (ι → ℝ) → ℝ) (A : ι → ι → (ι → ℝ) → ℝ)
    (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Periodic1 (B a))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Periodic1 c)
    (hc' : ContDiff ℝ (⊤ : ℕ∞) c') (hc'p : Periodic1 c')
    (k : ℕ) (p q : (ι → ℝ) → ℂ) (hp : SmoothPer p) (hq : SmoothPer q) :
    L2re (POp c c' (varLapOp A B) k p) q
      = L2re p (compOp (compOp (mulOp c) ((varLapStarOp A (fun a => -B a))^[k]))
          (mulOp c') q) := by
  have hmul : SmoothPer (mulOp c p) := SmoothPer.mulOp' hc hcp hp
  have hmul' : SmoothPer (mulOp c' q) := SmoothPer.mulOp' hc' hc'p hq
  rw [show POp c c' (varLapOp A B) k p
        = mulOp c' (((varLapOp A B)^[k]) (mulOp c p)) from rfl]
  rw [mulOp_L2re_adjoint]
  rw [varLapPow_L2re_adjoint A B hA hAp hB hBp k (mulOp c p) (mulOp c' q) hmul hmul']
  rw [mulOp_L2re_adjoint]
  rfl

/-! ## 8. The target -/

theorem POp_adjoint_L2re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {c c' : (ι → ℝ) → ℝ}
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Work.Diff.STE.Periodic1 c)
    (hc' : ContDiff ℝ (⊤ : ℕ∞) c') (hc'p : Work.Diff.STE.Periodic1 c')
    (p q : (ι → ℝ) → ℂ)
    (hp : Work.Diff.STE.B3.VarCoef.SmoothPer p) (hq : Work.Diff.STE.B3.VarCoef.SmoothPer q) :
    Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.POp c c'
        (Work.Diff.STE.B3.VarCoef.varLapOp A B) k p) q
      = Work.Diff.STE.L2re p (Work.Diff.STE.B3.VarCoef.POpStar c c' A
          (fun a => -B a) k q) := by
  rw [show POpStar c c' A (fun a => -B a) k q
        = compOp (compOp (mulOp c) ((varLapStarOp A (fun a => -B a))^[k]))
            (mulOp c') q from rfl]
  exact POp_L2re_adjoint c c' A B hA hAp hB hBp hc hcp hc' hc'p k p q hp hq

end Work.Diff.STE.B3.VarCoef
