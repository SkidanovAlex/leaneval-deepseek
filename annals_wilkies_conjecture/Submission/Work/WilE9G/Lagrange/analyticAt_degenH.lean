/-
  WilE9G / Lagrange — analyticity of the genericity system `degenH`.

  `degenH S Phi` is the system
    `(h_a(z), degenLam(z,ν,ν₀), degenPsi_l(z,ν,ν₀,c))_l`
  whose entries are built from the `z`-, `ν`- and `c`-coordinate projections by
  forming `eaEval` of the (fixed) polynomials of `S` and `Phi` at the `z`-part,
  then multiplying by the multiplier coordinates and summing.  Every one of these
  operations preserves analyticity, so `degenH S Phi` is analytic everywhere.

  The only lift required is that a coordinate projection `p ↦ p i` on `Fin k → ℝ`
  is analytic (it is continuous linear), together with `AnalyticAt.pi` to handle
  the Pi-valued maps `degenZ`, `degenNu`, `degenC`, and
  `Work.WilE5.Strat.analyticAt_eaEval` for the analyticity of `eaEval`.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.DegenSetup
import Submission.Work.WilE5.Strat.flatConormalTools

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9G

variable {n m : ℕ}

/-! ## Analyticity of the coordinate projections -/

/-- The `i`-th coordinate projection on `Fin k → ℝ` is analytic. -/
lemma analyticAt_coord {k : ℕ} (p : Fin k → ℝ) (i : Fin k) :
    AnalyticAt ℝ (fun p : Fin k → ℝ => p i) p :=
  (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).analyticAt p

/-- The `i`-th coordinate of `degenZ` is analytic in the point. -/
lemma analyticAt_degenZ_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (i : Fin (n + (1 + m))) :
    AnalyticAt ℝ (fun p : Fin (degenDim n m j) → ℝ => degenZ p i) p := by
  exact (ContinuousLinearMap.proj (⟨i.val, by simp only [degenDim]; omega⟩ : Fin (degenDim n m j)) :
    (Fin (degenDim n m j) → ℝ) →L[ℝ] ℝ).analyticAt p

/-- The `a`-th coordinate of `degenNu` is analytic in the point. -/
lemma analyticAt_degenNu_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (a : Fin (j + 1)) :
    AnalyticAt ℝ (fun p : Fin (degenDim n m j) → ℝ => degenNu p a) p := by
  exact (ContinuousLinearMap.proj (⟨n + (1 + m) + a.val, by simp only [degenDim]; omega⟩ : Fin (degenDim n m j)) :
    (Fin (degenDim n m j) → ℝ) →L[ℝ] ℝ).analyticAt p

/-- The `l`-th coordinate of `degenC` is analytic in the point. -/
lemma analyticAt_degenC_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (l : Fin (1 + m)) :
    AnalyticAt ℝ (fun p : Fin (degenDim n m j) → ℝ => degenC p l) p := by
  exact (ContinuousLinearMap.proj (⟨n + (1 + m) + (j + 1) + l.val, by simp only [degenDim]; omega⟩ : Fin (degenDim n m j)) :
    (Fin (degenDim n m j) → ℝ) →L[ℝ] ℝ).analyticAt p

/-- The map `degenZ : ℝ^{degenDim} → ℝ^{n+(1+m)}` is analytic. -/
lemma analyticAt_degenZ {j : ℕ} (p : Fin (degenDim n m j) → ℝ) :
    AnalyticAt ℝ (degenZ (n := n) (m := m) (j := j)) p := by
  refine AnalyticAt.pi (fun i => ?_)
  exact analyticAt_degenZ_apply p i

/-! ## Analyticity of the pieces of the system -/

/-- `p ↦ eaEval S.X.c Q (degenZ p)` is analytic. -/
lemma analyticAt_eaEval_degenZ {j : ℕ} (S : AmbStratum (n + (1 + m)))
    (Q : EAPoly (n + (1 + m)) S.X.r) (p : Fin (degenDim n m j) → ℝ) :
    AnalyticAt ℝ (fun p : Fin (degenDim n m j) → ℝ => eaEval S.X.c Q (degenZ p)) p :=
  (Work.WilE5.Strat.analyticAt_eaEval S.X.c Q (degenZ p)).comp (analyticAt_degenZ p)

/-- The normalisation equation `degenLam` is analytic. -/
lemma analyticAt_degenLam (S : AmbStratum (n + (1 + m)))
    (p : Fin (degenDim n m S.j) → ℝ) :
    AnalyticAt ℝ (degenLam S) p := by
  change AnalyticAt ℝ
    (fun p : Fin (degenDim n m S.j) → ℝ => (∑ a : Fin (S.j + 1), (degenNu p a) ^ 2) - 1) p
  have h1 : AnalyticAt ℝ
      (fun p : Fin (degenDim n m S.j) → ℝ => ∑ a : Fin (S.j + 1), (degenNu p a) ^ 2) p := by
    have h2 := Finset.analyticAt_sum (Finset.univ : Finset (Fin (S.j + 1)))
      (fun a _ => (analyticAt_degenNu_apply p a).pow 2)
    convert h2 using 1
    ext q
    simp [Finset.sum_apply]
  exact h1.sub analyticAt_const

/-- The `l`-th Lagrange equation `degenPsi · l` is analytic. -/
lemma analyticAt_degenPsi (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) :
    AnalyticAt ℝ (fun p : Fin (degenDim n m S.j) → ℝ => degenPsi S Phi p l) p := by
  have hnu0 : AnalyticAt ℝ
      (fun p : Fin (degenDim n m S.j) → ℝ => degenNu p (Fin.last S.j)) p :=
    analyticAt_degenNu_apply p (Fin.last S.j)
  have hA : AnalyticAt ℝ
      (fun p : Fin (degenDim n m S.j) → ℝ => eaEval S.X.c Phi (degenZ p)) p :=
    analyticAt_eaEval_degenZ S Phi p
  have hB : AnalyticAt ℝ (fun p : Fin (degenDim n m S.j) → ℝ =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) (degenZ p)) p :=
    analyticAt_eaEval_degenZ S (eaD S.X.c (Fin.natAdd n l) Phi) p
  have hC : AnalyticAt ℝ (fun p : Fin (degenDim n m S.j) → ℝ => degenC p l) p :=
    analyticAt_degenC_apply p l
  have hsum : AnalyticAt ℝ (fun p : Fin (degenDim n m S.j) → ℝ =>
      ∑ a : Fin S.j, degenNu p (Fin.castAdd 1 a)
        * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p)) p := by
    have h2 := Finset.analyticAt_sum (Finset.univ : Finset (Fin S.j))
      (fun a _ => (analyticAt_degenNu_apply p (Fin.castAdd 1 a)).mul
        (analyticAt_eaEval_degenZ S (eaD S.X.c (Fin.natAdd n l) (S.h a)) p))
    convert h2 using 1
    ext q
    simp [Finset.sum_apply]
  change AnalyticAt ℝ (fun p : Fin (degenDim n m S.j) → ℝ =>
      degenNu p (Fin.last S.j)
        * (eaEval S.X.c Phi (degenZ p) * degenC p l
            + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) (degenZ p))
      - ∑ a : Fin S.j, degenNu p (Fin.castAdd 1 a)
          * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p)) p
  exact (hnu0.mul ((hA.mul hC).add hB)).sub hsum

/-! ## The system `degenH` -/

/-- The system `degenH S Phi` is analytic. -/
theorem analyticAt_degenH {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (Work.WilE9G.Lagrange.degenDim n m S.j) → ℝ) :
    AnalyticAt ℝ (Work.WilE9G.Lagrange.degenH S Phi) p := by
  show AnalyticAt ℝ (fun x : Fin (degenDim n m S.j) → ℝ =>
    fun i : Fin (S.j + (1 + (1 + m))) => degenH S Phi x i) p
  refine AnalyticAt.pi (fun i => ?_)
  refine Fin.addCases (motive := fun i =>
    AnalyticAt ℝ (fun p : Fin (degenDim n m S.j) → ℝ => degenH S Phi p i) p) ?_ ?_ i
  · intro a
    simp only [degenH, Fin.append_left]
    exact analyticAt_eaEval_degenZ S (S.h a) p
  · intro b
    simp only [degenH, Fin.append_right]
    refine Fin.addCases (motive := fun b => AnalyticAt ℝ
      (fun p : Fin (degenDim n m S.j) → ℝ =>
        Fin.append (fun _ : Fin 1 => degenLam S p)
          (fun l : Fin (1 + m) => degenPsi S Phi p l) b) p) ?_ ?_ b
    · intro u
      simp only [Fin.append_left]
      exact analyticAt_degenLam S p
    · intro l
      simp only [Fin.append_right]
      exact analyticAt_degenPsi S Phi p l

end Work.WilE9G.Lagrange
