/-
  WilC5 — `n`-th roots of squares in a model of `T_r`.

  Let `M ⊨ T_r` be a model of the theory of `ℝ_rexp` (with all reals named by constants), together
  with a compatible `Field`, `LinearOrder`, `IsStrictOrderedRing` structure — this is exactly the
  "ordered field" reading of `M` used in the amalgamation arguments of C5 / vdDMM §4.

  The claim is that for every `b : M` and every `n ≥ 1` there is `z` with `z ^ n = b ^ 2`.  This is
  the statement that `M` is a real closed field: every non-negative element is an `n`-th power, and
  `b ^ 2 ≥ 0`.

  The proof is by the standard transfer of this workspace: the `ring`-sentence

      `σ_n  :=  ∀ x, ∃ z, z ^ n = x * x`

  is true in `ℝ` (take `z = (x*x) ^ (1/n)`, a real `rpow`), hence belongs to `T_r` (the complete
  `LRc`-theory of `ℝ`), and the embedding of the language of rings into `LRc` transfers it to `M`.
  Because the `Language.ring.Structure` of `M` is compatible with its `Field` structure, the
  realization of `σ_n` at `b` is literally `∃ z : M, z ^ n = b ^ 2`.

  This is the `n`-th root companion of `WilC2/Square.lean` (`model_exists_sq`, the `n = 2` case
  with `b = 1`), and it is used to close `WilC5/ElemChain.lean`'s `elemSub_pow_root`.
-/
import Mathlib
import Submission.Work.WilC5.tr_leE_axioms
import Submission.Work.WilC2.Square

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC5

open WilkiesDesign.CG (LR LRc TR rexpL)

/-! ## 1. Iterated products in the language of rings -/

/-- The `n`-fold product `t * t * ⋯ * t` (with `0`-fold product `1`), as a term of the language
of rings. -/
def ringPowTerm {α : Type*} (n : ℕ) (t : Language.ring.Term α) : Language.ring.Term α :=
  match n with
  | 0 => 1
  | m + 1 => ringPowTerm m t * t

/-- Realization of `ringPowTerm`: it is the `n`-th power of the realization of `t`. -/
theorem realize_ringPowTerm {R : Type*} [Ring R] [FirstOrder.Ring.CompatibleRing R]
    {α : Type*} (n : ℕ) (t : Language.ring.Term α) (v : α → R) :
    Term.realize v (ringPowTerm n t) = (Term.realize v t) ^ n := by
  induction n with
  | zero => simp [ringPowTerm]
  | succ n ih => rw [ringPowTerm, Ring.realize_mul, ih, pow_succ]

/-! ## 2. The sentence `∀ x, ∃ z, z ^ n = x * x` of the language of rings -/

/-- The ring formula `z ^ n = x * x`: the middle block of variables is `x`, the last block is the
bound variable `z` (mirroring the convention of `WilC2/Square.lean`). -/
def powBody (n : ℕ) : Language.ring.Formula ((Empty ⊕ Fin 1) ⊕ Fin 1) :=
  Term.equal (ringPowTerm n (Term.var (Sum.inr (0 : Fin 1))))
    (Term.var (Sum.inl (Sum.inr (0 : Fin 1))) * Term.var (Sum.inl (Sum.inr (0 : Fin 1))))

/-- The ring sentence `∀ x, ∃ z, z ^ n = x * x`. -/
def powSent (n : ℕ) : Language.ring.Sentence := (powBody n).iExs (Fin 1) |>.iAlls (Fin 1)

/-- Semantic characterization of `powSent n`. -/
theorem powSent_realize {R : Type*} [Ring R] [FirstOrder.Ring.CompatibleRing R] (n : ℕ) :
    R ⊨ powSent n ↔ ∀ x : R, ∃ z : R, z ^ n = x ^ 2 := by
  simp only [Sentence.Realize, powSent, powBody, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_equal, realize_ringPowTerm, Ring.realize_mul, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, pow_two]
  constructor
  · rintro h x
    obtain ⟨z, hz⟩ := h (fun _ => x)
    exact ⟨z 0, hz⟩
  · rintro h i
    obtain ⟨z, hz⟩ := h (i 0)
    exact ⟨fun _ => z, hz⟩

/-- The sentence holds in `ℝ`: for every real `x` the non-negative number `x * x` has an `n`-th
root, namely `(x * x) ^ (1 / n)`. -/
theorem real_realize_powSent {n : ℕ} (hn : 1 ≤ n) : ℝ ⊨ powSent n := by
  rw [powSent_realize]
  intro x
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hx : (0 : ℝ) ≤ x * x := mul_self_nonneg x
  refine ⟨(x * x) ^ (1 / (n : ℝ)), ?_⟩
  calc ((x * x) ^ (1 / (n : ℝ))) ^ n
      = ((x * x) ^ (1 / (n : ℝ))) ^ (n : ℝ) := (Real.rpow_natCast _ n).symm
    _ = (x * x) ^ ((1 / (n : ℝ)) * (n : ℝ)) := (Real.rpow_mul hx _ _).symm
    _ = (x * x) ^ (1 : ℝ) := by rw [one_div_mul_cancel hn0]
    _ = x * x := Real.rpow_one _
    _ = x ^ 2 := (pow_two x).symm

/-! ## 3. The main theorem -/

/-- **Every element of a model of `T_r` has an `n`-th root of its square.** -/
theorem model_pow_root {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR)
    (b : M) {n : ℕ} (hn : 1 ≤ n) :
    ∃ z : M, z ^ n = b ^ 2 := by
  haveI hMT : M ⊨ LRc.completeTheory ℝ := hM
  haveI hExp : Work.WilC2.ringToLRc.IsExpansionOn M :=
    Work.WilC2.instRingToLRcIsExpansionOn M
  have hℝ : ℝ ⊨ Work.WilC2.ringToLRc.onSentence (powSent n) :=
    (LHom.realize_onSentence (M := ℝ) Work.WilC2.ringToLRc (powSent n)).mpr
      (real_realize_powSent hn)
  have h1 : M ⊨ Work.WilC2.ringToLRc.onSentence (powSent n) :=
    Theory.realize_sentence_of_mem (M := M) (T := LRc.completeTheory ℝ)
      (mem_completeTheory.mpr hℝ)
  have h2 : M ⊨ powSent n :=
    (LHom.realize_onSentence (M := M) Work.WilC2.ringToLRc (powSent n)).mp h1
  obtain ⟨z, hz⟩ := ((powSent_realize (R := M) n).mp h2) b
  exact ⟨z, hz⟩

end Work.WilC5
