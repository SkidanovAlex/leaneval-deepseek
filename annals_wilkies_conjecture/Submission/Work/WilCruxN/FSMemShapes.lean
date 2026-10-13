import Mathlib
import Submission.Work.WilCruxN.FSMemAux

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilCruxN.FSA

open WilkiesDesign WilkiesDesign.CG
open Work.WilG4c

/-! ## 7. The modulus set (second conjunct) -/

/-- The block of fibre coordinates inside `ℝ^{a+b}`. -/
def zIdx (a b : ℕ) (j : Fin b) : Fin (a + b) := Fin.natAdd a j

/-- `{x : ℝ^{a+b} | |f x_par x_fib| < d}`, via the graph atom. -/
def modFun (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (d : ℝ) : PKS S F D (a + b) :=
  PKS.exi (PKS.conj (PKS.mem (famGraph f) hG id)
    (PKS.conj
      (ltS S F D (MvPolynomial.X (Fin.last (a + b))) (MvPolynomial.C d) (td_X4 _) (td_C4 d))
      (ltS S F D (-(MvPolynomial.C d)) (MvPolynomial.X (Fin.last (a + b)))
        (td_negC4 d) (td_X4 _))))

theorem modFun_Real (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1)) (d : ℝ) :
    (modFun S F D f hG d).Real =
      {x : Fin (a + b) → ℝ |
        |f (fun i : Fin a => x (Fin.castAdd b i)) (fun j : Fin b => x (Fin.natAdd a j))| < d} := by
  ext x
  simp only [modFun, PKS.Real_exi, projLast, Set.mem_ofPred_eq, PKS.Real_conj,
    Set.mem_inter_iff, PKS.Real_mem, Function.comp_id, ltS_Real,
    MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_neg, Fin.snoc_last]
  constructor
  · rintro ⟨t, hg, h1, h2⟩
    rw [mem_famGraph_snoc] at hg
    rw [← hg]
    exact abs_lt.mpr ⟨h2, h1⟩
  · intro h
    refine ⟨f (fun i : Fin a => x (Fin.castAdd b i)) (fun j : Fin b => x (Fin.natAdd a j)),
      ?_, (abs_lt.mp h).2, (abs_lt.mp h).1⟩
    rw [mem_famGraph_snoc]

/-- The modulus shape. -/
def modShape (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (c d : ℝ) (hBall : ballConstSet b c ∈ S.Ω F D b) : PKS S F D a :=
  PKS.allb (k := b)
    (PKS.imp
      (PKS.conj (sumSqNe S F D (zIdx a b))
        (PKS.mem (ballConstSet b c) hBall (zIdx a b)))
      (modFun S F D f hG d))

theorem modShape_Real (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (c d : ℝ) (hBall : ballConstSet b c ∈ S.Ω F D b) :
    (modShape S F D f hG c d hBall).Real =
      {w : Fin a → ℝ | ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < c → |f w z| < d} := by
  ext w
  rw [modShape, PKS.Real_allb]
  simp only [Set.mem_ofPred_eq]
  refine forall_congr' (fun v => ?_)
  rw [PKS.Real_imp, PKS.Real_conj, sumSqNe_Real, PKS.Real_mem, modFun_Real]
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Function.comp_apply, ballConstSet, zIdx, Fin.append_left, Fin.append_right]
  have hfun : ((fun j : Fin b => v j) ≠ (0 : Fin b → ℝ)) ↔ v ≠ 0 := by
    simp only [ne_eq, funext_iff, Pi.zero_apply]
  rw [hfun]
  constructor
  · rintro (h | h) hv0 hvc
    · exact absurd ⟨hv0, (norm_lt_iff_forall_abs hv0).mp hvc⟩ h
    · exact h
  · intro h
    by_cases hpre : v ≠ 0 ∧ ∀ j, |v j| < c
    · exact Or.inr (h hpre.1 ((norm_lt_iff_forall_abs hpre.1).mpr hpre.2))
    · exact Or.inl hpre

/-! ## The format and atom count of `modShape` are independent of the data -/

lemma modShape_Fmt_eq (S : SOMin) (F : ℕ) {a b : ℕ} (D₁ D₂ : ℕ)
    (f₁ : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG₁ : famGraph f₁ ∈ S.Ω F D₁ (a + b + 1))
    (c₁ d₁ : ℝ) (hB₁ : ballConstSet b c₁ ∈ S.Ω F D₁ b)
    (f₂ : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG₂ : famGraph f₂ ∈ S.Ω F D₂ (a + b + 1))
    (c₂ d₂ : ℝ) (hB₂ : ballConstSet b c₂ ∈ S.Ω F D₂ b) :
    (modShape S F D₁ f₁ hG₁ c₁ d₁ hB₁).Fmt = (modShape S F D₂ f₂ hG₂ c₂ d₂ hB₂).Fmt := rfl

lemma modShape_Atoms_eq (S : SOMin) (F : ℕ) {a b : ℕ} (D₁ D₂ : ℕ)
    (f₁ : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG₁ : famGraph f₁ ∈ S.Ω F D₁ (a + b + 1))
    (c₁ d₁ : ℝ) (hB₁ : ballConstSet b c₁ ∈ S.Ω F D₁ b)
    (f₂ : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG₂ : famGraph f₂ ∈ S.Ω F D₂ (a + b + 1))
    (c₂ d₂ : ℝ) (hB₂ : ballConstSet b c₂ ∈ S.Ω F D₂ b) :
    (modShape S F D₁ f₁ hG₁ c₁ d₁ hB₁).Atoms
      = (modShape S F D₂ f₂ hG₂ c₂ d₂ hB₂).Atoms := rfl

end Work.WilCruxN.FSA
