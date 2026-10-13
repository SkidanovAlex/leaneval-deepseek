/-
  WilG4c / `StepLipHighPsiAux2` — small `Ω`/polynomial bookkeeping lemmas used by the
  proof of `Work.WilkG4c.StepLipHighPsiCond` (BNZ §5.3, the per-chart step).

  Everything here is `sorry`-free.  The file deliberately avoids the modules of the
  `EpsSetDefs` chain (they clash with `ValSetDefs` on `Work.WilG4c.wIdx`).
-/
import Mathlib
import Submission.Work.WilG4c.StepLipHighOuter
import Submission.Work.WilkG4c.StepTupleMem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. A `k`-uniform form of `StepTupleMem`

In the assembly the format `Ftup` and the degree polynomial `dtup` of the §5.3 tuple have to be
chosen *before* the number `k` of family members (they are witnesses of the `∃ a b c` prefix of
`FLemP`).  `Work.WilkG4c.StepTupleMem` takes `k` as an argument, so its witnesses may in
principle depend on `k`; its proof shows that they do not, and this lemma makes that explicit. -/
theorem stepTupleMemU (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∀ (F0 Ag : ℕ) (Bg : MvPolynomial (Fin 2) ℕ), ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (k : ℕ) (D : ℕ) (G : Work.WilkG4c.Family k p (n + 1))
        (γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ)),
        (∀ i, WilkiesDesign.CG.famGraph (G i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        (∀ (i : Fin k) (j : Fin n), WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
            γ i (Fin.init w) (w (Fin.last p)) j)
              ∈ S.Ω Ag (MvPolynomial.eval ![D, 0] Bg) (p + 1 + 1)) →
        (WilkiesDesign.CG.famGraph (fun (_ : Fin p → ℝ) (u : Fin 1 → ℝ) => u 0)
            ∈ S.Ω A (MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg] B) (p + 1 + 1)) ∧
        (∀ (i : Fin k) (j : Fin n), WilkiesDesign.CG.famGraph
            (fun (l : Fin p → ℝ) (u : Fin 1 → ℝ) => γ i l (u 0) j)
              ∈ S.Ω A (MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg] B) (p + 1 + 1)) ∧
        (∀ i : Fin k, WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (u : Fin 1 → ℝ) =>
            G i l (Fin.cons (u 0) (γ i l (u 0))))
              ∈ S.Ω A (MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg] B) (p + 1 + 1)) := by
  intro F0 Ag Bg
  obtain ⟨Ac, Cc, hCc⟩ := Work.WilG4c.ConsCompFamGraphMem S p n
  refine ⟨max (p + 1 + 1) (max Ag (F0 + Ag + Ac)),
    MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
      + MvPolynomial.C Cc, ?_⟩
  intro k D G γ hG hγ
  have hA1 : p + 1 + 1 ≤ max (p + 1 + 1) (max Ag (F0 + Ag + Ac)) := le_max_left _ _
  have hA2 : Ag ≤ max (p + 1 + 1) (max Ag (F0 + Ag + Ac)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hA3 : F0 + Ag + Ac ≤ max (p + 1 + 1) (max Ag (F0 + Ag + Ac)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hpn : 1 ≤ p + (n + 1) := by omega
  have hval : MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg]
      (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
        + MvPolynomial.C Cc) =
      D + (p + (n + 1)) * (MvPolynomial.eval ![D, 0] Bg + 1) + Cc := by
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul]
  have hmul : 1 * (MvPolynomial.eval ![D, 0] Bg + 1)
      ≤ (p + (n + 1)) * (MvPolynomial.eval ![D, 0] Bg + 1) :=
    Nat.mul_le_mul_right _ hpn
  have hle1 : (1 : ℕ) ≤ MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg]
      (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
        + MvPolynomial.C Cc) := by
    rw [hval]; omega
  have hle2 : MvPolynomial.eval ![D, 0] Bg ≤
      MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg]
      (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
        + MvPolynomial.C Cc) := by
    rw [hval]; omega
  have hle3 : D + (p + (n + 1)) * (MvPolynomial.eval ![D, 0] Bg + 1) + Cc ≤
      MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg]
      (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
        + MvPolynomial.C Cc) := le_of_eq hval.symm
  refine ⟨?_, ?_, ?_⟩
  · exact Work.WilkG4c.Omega_mono_le S hA1 hle1 (Work.WilkG4c.famGraph_identity_mem S p)
  · intro i j
    exact Work.WilkG4c.Omega_mono_le S hA2 hle2 (hγ i j)
  · intro i
    exact Work.WilkG4c.Omega_mono_le S hA3 hle3
      (hCc F0 D Ag (MvPolynomial.eval ![D, 0] Bg) (G i) (γ i) (hG i)
        (fun j => by simpa only [Fin.init_def] using hγ i j))

/-! ## 2. Polynomial bookkeeping -/

/-- A polynomial in `Fin 1` (equivalently a `Polynomial ℕ`) as a two-variable polynomial whose
evaluation at `![D,r]` is the value at `D` — constant in the second variable. -/
theorem polyConstSecond (c : Polynomial ℕ) :
    ∃ q : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ, MvPolynomial.eval ![D, r] q = c.eval D :=
  ⟨Polynomial.toMvPolynomial (0 : Fin 2) c, fun D r => by
    rw [MvPolynomial.eval_toMvPolynomial]; rfl⟩

/-- Substituting a two-variable polynomial into the first variable of another, and the second
variable by the constant `1`. -/
theorem polySubstFirstOne (q : MvPolynomial (Fin 2) ℕ) (b : Polynomial ℕ) :
    ∃ B : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![D, r] B = b.eval (MvPolynomial.eval ![D, r] q) := by
  obtain ⟨q₀, hq₀⟩ := polyConstSecond b
  refine ⟨MvPolynomial.aeval ![q, MvPolynomial.X 1] q₀, fun D r => ?_⟩
  rw [Work.WilG4c.eval_aeval_eq]
  have hfun : (fun i : Fin 2 => MvPolynomial.eval ![D, r]
      (![q, MvPolynomial.X 1] i)) = ![MvPolynomial.eval ![D, r] q, r] := by
    funext i; fin_cases i <;> simp
  rw [hfun, hq₀]



/-! ## 3. The slab `x ∈ I` as an Ω-set -/

/-- `z ∈ inCubeSet p 1` says that the distinguished coordinate lies in `I`. -/
theorem mem_inCubeSet_one' {p : ℕ} {z : Fin (p + 1) → ℝ} :
    z ∈ Work.WilG4c.inCubeSet p 1 ↔ z (Fin.last p) ∈ Work.WilkG4c.I := by
  rw [Work.WilG4c.inCubeSet]
  simp only [Set.mem_ofPred_eq]
  have h0 : Fin.natAdd p (0 : Fin 1) = Fin.last p := by ext; simp [Fin.natAdd, Fin.last]
  simp only [WilkiesDesign.openCube, Work.WilkG4c.I, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · intro h; rw [← h0]; exact h 0
  · intro h j; rw [Fin.eq_zero j, h0]; exact h

end Work.WilkG4c
