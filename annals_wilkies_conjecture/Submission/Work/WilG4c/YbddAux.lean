/-
  WilG4c / StepYbdd — BNZ §5.2, the reduction to bounded `y`-derivatives.

  This file proves `Work.WilkG4c.StepYbdd`: from the F-lemma in dimension `n` (`ih`) and the
  F-lemma for families whose `y`-derivatives are globally bounded by `1` (`hP0`, i.e.
  `FLemP S p (n+1) (PY p n)`), deduce the F-lemma in dimension `n+1`.

  The mathematical argument is the one of BNZ §5.2, with one extra device needed by the
  *global* form of the hypothesis `PY`: the inductive hypothesis is applied to the
  **clamped** family `clampFam F` (values pushed into `(0,1)`) over the *whole* parameter
  space `{w | w last ∈ I}`; this makes the pulled-back family `G_η = clampFam F ∘ φ_η`
  globally `y`-bounded, so that `hP0` applies to it.  On the cube the clamp is the identity,
  so the resulting charts are charts for the original `F`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Subst
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.API
import Submission.Work.WilG0.projLastIter_mem

set_option autoImplicit false

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1
open scoped BigOperators

noncomputable section
open Classical

/-! ## 1. Definitions -/

/-- Clamp a real number into the open unit interval: the identity on `(0,1)`, the constant
`1/2` elsewhere. -/
def yclamp (t : ℝ) : ℝ := if t ∈ Set.Ioo (0 : ℝ) 1 then t else 1 / 2

theorem yclamp_of_mem {t : ℝ} (h : t ∈ Set.Ioo (0 : ℝ) 1) : yclamp t = t := by
  simp [yclamp, h]

theorem yclamp_mem (t : ℝ) : yclamp t ∈ Set.Ioo (0 : ℝ) 1 := by
  by_cases h : t ∈ Set.Ioo (0 : ℝ) 1
  · simpa [yclamp, h] using h
  · simp only [yclamp, h, ite_false]
    norm_num

/-- The family obtained by clamping every value into `(0,1)`. -/
def clampFam {k p m : ℕ} (F : Family k p m) : Family k p m := fun i l u => yclamp (F i l u)

/-- Regroup a family of `n+1`-variable functions as a family of `n`-variable functions over the
parameter space with the first coordinate adjoined at the end. -/
def vie {k p n : ℕ} (F : Family k p (n + 1)) : Family k (p + 1) n :=
  fun i w y => F i (fun a : Fin p => w a.castSucc) (Fin.cons (w (Fin.last p)) y)

/-- The point map of the chart of the `(n+1)`-cube induced by a chart `φ` of the `n`-cube over
the parameter space with the first coordinate adjoined. -/
def phiPt {p n : ℕ} (φ : ChartTuple (p + 1) n) (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun j => Fin.cases (z 0) (fun i : Fin n => φ i (parSnoc l (z 0)) (Fin.tail z)) j

@[simp] theorem phiPt_zero {p n : ℕ} (φ : ChartTuple (p + 1) n) (l : Fin p → ℝ)
    (z : Fin (n + 1) → ℝ) : phiPt φ l z 0 = z 0 := by
  simp [phiPt]

@[simp] theorem phiPt_succ {p n : ℕ} (φ : ChartTuple (p + 1) n) (l : Fin p → ℝ)
    (z : Fin (n + 1) → ℝ) (i : Fin n) :
    phiPt φ l z i.succ = φ i (parSnoc l (z 0)) (Fin.tail z) := by
  simp [phiPt]

/-- Pull back a family by `phiPt φ`. -/
def pullFam {k p n : ℕ} (F : Family k p (n + 1)) (φ : ChartTuple (p + 1) n) :
    Family k p (n + 1) :=
  fun i l z => F i l (phiPt φ l z)

/-- The composite chart of the `(n+1)`-cube. -/
def chartComp {p n : ℕ} (φ : ChartTuple (p + 1) n) (ψ : ChartTuple p (n + 1)) :
    ChartTuple p (n + 1) :=
  ofPt (fun l z => phiPt φ l (toPt ψ l z))

@[simp] theorem chartComp_apply {p n : ℕ} (φ : ChartTuple (p + 1) n) (ψ : ChartTuple p (n + 1))
    (j : Fin (n + 1)) (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) :
    chartComp φ ψ j l z = phiPt φ l (toPt ψ l z) j := rfl

theorem vie_clampFam_eq {k p n : ℕ} (F : Family k p (n + 1)) (i : Fin k) :
    vie (clampFam F) i = fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
      (if F i (fun a : Fin p => w a.castSucc) (Fin.cons (w (Fin.last p)) y)
          ∈ Set.Ioo (0 : ℝ) 1
       then F i (fun a : Fin p => w a.castSucc) (Fin.cons (w (Fin.last p)) y) else 1 / 2) := by
  funext w y
  simp only [vie, clampFam, yclamp]

theorem clampFam_eq_of_mem {k p m : ℕ} (F : Family k p m) (i : Fin k) (l : Fin p → ℝ)
    (u : Fin m → ℝ) (h : F i l u ∈ Set.Ioo (0 : ℝ) 1) : clampFam F i l u = F i l u := by
  simp only [clampFam, yclamp_of_mem h]

theorem vie_parSnoc {k p n : ℕ} (F : Family k p (n + 1)) (i : Fin k) (l : Fin p → ℝ)
    (x : ℝ) (t : Fin n → ℝ) : vie F i (parSnoc l x) t = F i l (Fin.cons x t) := by
  simp only [vie, parSnoc_castSucc, parSnoc_last]

theorem phiPt_pt {p n : ℕ} (φ : ChartTuple (p + 1) n) (l : Fin p → ℝ) (x : ℝ)
    (t : Fin n → ℝ) :
    phiPt φ l (pt x t) = Fin.cons x (fun j => φ j (parSnoc l x) t) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [phiPt]
  | succ i => simp [phiPt, tail_pt]

theorem slice_pullFam {k p n : ℕ} (F : Family k p (n + 1)) (φ : ChartTuple (p + 1) n)
    (i : Fin k) (l : Fin p → ℝ) (x : ℝ) :
    slice (pullFam F φ i l) x
      = fun t => vie F i (parSnoc l x) (fun j => φ j (parSnoc l x) t) := by
  funext t
  simp only [slice_apply, pullFam]
  rw [phiPt_pt]
  simp only [vie, parSnoc_castSucc, parSnoc_last]

theorem openCube_isOpen (m : ℕ) : IsOpen (openCube m) := by
  have h : openCube m = ⋂ i : Fin m, {t : Fin m → ℝ | t i ∈ Set.Ioo (0 : ℝ) 1} := by
    ext t; simp [openCube]
  rw [h]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

/-! ## 2. The graph of a coordinate projection -/

theorem graphOf_coord_mem (S : SOMin) {N : ℕ} (i : Fin N) :
    graphOf (fun x : Fin N → ℝ => x i) ∈ S.Ω (N + 1) 1 (N + 1) := by
  have h := S.hyp (N + 1)
    (MvPolynomial.X (Fin.last N) - MvPolynomial.X (i.castSucc) : MvPolynomial (Fin (N + 1)) ℝ)
  have hdeg : (MvPolynomial.X (Fin.last N) - MvPolynomial.X (i.castSucc) :
      MvPolynomial (Fin (N + 1)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩
  have hset : {x : Fin (N + 1) → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (Fin.last N) - MvPolynomial.X (i.castSucc) :
          MvPolynomial (Fin (N + 1)) ℝ) = 0}
      = graphOf (fun x : Fin N → ℝ => x i) := by
    ext z
    simp only [Set.mem_ofPred_eq, graphOf, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      sub_eq_zero, Fin.init]
  rw [hset] at h
  exact Omega.mono h le_rfl hdeg

/-! ## 3. Uniform composition of `Ω`-definable maps

`Work.WilG4c.GraphOfComp` returns the format/degree increments *existentially after* the data;
the reductions of BNZ §5.2 need them *uniformly* in the data, so we record the explicit
constants of that proof. -/

/-- **Composition of `Ω`-definable maps, with explicit constants.** -/
theorem graphOf_comp_exp (S : SOMin) (m : ℕ) :
    ∃ (C₁ C₂ : ℕ), ∀ (F₁ F₂ D₁ D₂ : ℕ) (g : (Fin m → ℝ) → ℝ)
      (φ : (Fin m → ℝ) → (Fin m → ℝ)),
      graphOf g ∈ S.Ω F₁ D₁ (m + 1) →
      (∀ j, graphOf (fun x : Fin m → ℝ => φ x j) ∈ S.Ω F₂ D₂ (m + 1)) →
      graphOf (g ∘ φ) ∈ S.Ω (F₁ + F₂ + C₁) (D₁ + m * D₂ + C₂) (m + 1) := by
  refine ⟨2 * (((m + 1) + m) + (m + 1)) + 1 + 1 + 1 + m + (m + 1), 2 + 2 * m, ?_⟩
  intro F₁ F₂ D₁ D₂ g φ hg hφ
  have hG : Work.WilG4c.GraphComp.setG m g ∈ S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1))
      (D₁ + 2) ((m + 1) + m) :=
    Omega.mono (Work.WilG4c.GraphComp.subst_mem S (Work.WilG4c.GraphComp.sigG m) hg)
      (by omega) le_rfl
  have hH : ∀ j : Fin m, Work.WilG4c.GraphComp.setH m φ j ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1)) (D₂ + 2) ((m + 1) + m) :=
    fun j => Omega.mono
      (Work.WilG4c.GraphComp.subst_mem S (Work.WilG4c.GraphComp.sigPhi m j) (hφ j))
      (by omega) le_rfl
  have hA2 : (⋂ j : Fin m, Work.WilG4c.GraphComp.setH m φ j) ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1)
        (m * (D₂ + 2)) ((m + 1) + m) := by
    have h := S.inter (F := F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1))
      (n := (m + 1) + m) (D := fun _ : Fin m => D₂ + 2)
      (A := fun j : Fin m => Work.WilG4c.GraphComp.setH m φ j) hH
    have hsum : (∑ _ : Fin m, (D₂ + 2)) = m * (D₂ + 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    rw [hsum] at h
    exact h
  have hG' : Work.WilG4c.GraphComp.setG m g ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1)
      (D₁ + 2) ((m + 1) + m) := Omega.mono hG (by omega) le_rfl
  have hInt : (Work.WilG4c.GraphComp.setG m g ∩ ⋂ j : Fin m, Work.WilG4c.GraphComp.setH m φ j) ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1)
        ((D₁ + 2) + m * (D₂ + 2)) ((m + 1) + m) := Omega_inter2 hG' hA2
  have hProj : projLastIter (m + 1) m
      (Work.WilG4c.GraphComp.setG m g ∩ ⋂ j : Fin m, Work.WilG4c.GraphComp.setH m φ j) ∈
      S.Ω ((F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1) + m + (m + 1))
        ((D₁ + 2) + m * (D₂ + 2)) (m + 1) :=
    Work.WilG0.projLastIter_mem S (m + 1) m
      (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1)
      ((D₁ + 2) + m * (D₂ + 2)) _ hInt
  have hset : projLastIter (m + 1) m
      (Work.WilG4c.GraphComp.setG m g ∩ ⋂ j : Fin m, Work.WilG4c.GraphComp.setH m φ j)
        = graphOf (g ∘ φ) := by
    rw [Work.WilG0.projLastIter_eq]
    ext x
    constructor
    · rintro ⟨w, hw⟩
      rw [Set.mem_inter_iff] at hw
      obtain ⟨hGm, hHm⟩ := hw
      rw [Set.mem_iInter] at hHm
      have hlast : x (Fin.last m) = g w := (Work.WilG4c.GraphComp.mem_setG g x w).mp hGm
      have hwx : w = φ (Fin.init x) := by
        funext j
        exact (Work.WilG4c.GraphComp.mem_setH φ j x w).mp (hHm j)
      rw [hwx] at hlast
      simpa [graphOf] using hlast
    · intro hx
      have hx' : x (Fin.last m) = g (φ (Fin.init x)) := by simpa [graphOf] using hx
      refine ⟨φ (Fin.init x), ?_⟩
      rw [Set.mem_inter_iff, Set.mem_iInter]
      exact ⟨(Work.WilG4c.GraphComp.mem_setG g x (φ (Fin.init x))).mpr hx',
        fun j => (Work.WilG4c.GraphComp.mem_setH φ j x (φ (Fin.init x))).mpr rfl⟩
  rw [hset] at hProj
  have hF : ((F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1) + m + (m + 1)) ≤
      F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1 + 1 + 1 + m + (m + 1)) :=
    le_of_eq (by ring)
  have hD : (D₁ + 2) + m * (D₂ + 2) ≤ D₁ + m * D₂ + (2 + 2 * m) := le_of_eq (by ring)
  exact Omega.mono hProj hF hD

/-! ## 4. `famGraph` of a composition -/

/-- The "flattening" of a family member: `famGraph f = graphOf (flatFun f)`. -/
def flatFun {p m : ℕ} (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ) : (Fin (p + m) → ℝ) → ℝ :=
  fun z => f (fun i => z (Fin.castAdd m i)) (fun j => z (Fin.natAdd p j))

theorem famGraph_eq_graphOf_flatFun {p m : ℕ} (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ) :
    famGraph f = graphOf (flatFun f) := rfl

/-- The "flattening" of a chart. -/
def flatChart {p m : ℕ} (χ : Fin m → (Fin p → ℝ) → (Fin m → ℝ) → ℝ) :
    (Fin (p + m) → ℝ) → (Fin (p + m) → ℝ) :=
  fun x j => Fin.addCases (fun i : Fin p => x (Fin.castAdd m i))
    (fun k : Fin m => χ k (fun i => x (Fin.castAdd m i)) (fun k' => x (Fin.natAdd p k'))) j

theorem flatChart_castAdd {p m : ℕ} (χ : Fin m → (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (x : Fin (p + m) → ℝ) (i : Fin p) :
    flatChart χ x (Fin.castAdd m i) = x (Fin.castAdd m i) := by
  simp [flatChart]

theorem flatChart_natAdd {p m : ℕ} (χ : Fin m → (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (x : Fin (p + m) → ℝ) (k : Fin m) :
    flatChart χ x (Fin.natAdd p k)
      = χ k (fun i => x (Fin.castAdd m i)) (fun k' => x (Fin.natAdd p k')) := by
  simp [flatChart]

theorem graphOf_flatChart_castAdd {p m : ℕ} (χ : Fin m → (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (i : Fin p) :
    graphOf (fun x : Fin (p + m) → ℝ => flatChart χ x (Fin.castAdd m i))
      = graphOf (fun x : Fin (p + m) → ℝ => x (Fin.castAdd m i)) := by
  congr 1
  funext x
  exact flatChart_castAdd χ x i

theorem graphOf_flatChart_natAdd {p m : ℕ} (χ : Fin m → (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (k : Fin m) :
    graphOf (fun x : Fin (p + m) → ℝ => flatChart χ x (Fin.natAdd p k)) = famGraph (χ k) := by
  rw [famGraph_eq_graphOf_flatFun]
  congr 1
  funext x
  exact flatChart_natAdd χ x k

theorem flatFun_comp {p m : ℕ} (χ : Fin m → (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ) :
    flatFun (fun l z => f l (fun j => χ j l z)) = flatFun f ∘ flatChart χ := by
  funext x
  simp only [flatFun, Function.comp_apply, flatChart_castAdd, flatChart_natAdd]

/-- **`famGraph` of a composition.**  If the member `f` and the coordinates of the chart `χ`
have `Ω`-bounded graphs, then so does `l ↦ f l (χ l ·)`, uniformly in the data. -/
theorem famGraph_comp_single (S : SOMin) (p m : ℕ) :
    ∃ (a c : ℕ), ∀ (F0 F1 D0 D1 : ℕ) (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
      (χ : Fin m → (Fin p → ℝ) → (Fin m → ℝ) → ℝ),
      famGraph f ∈ S.Ω F0 D0 (p + m + 1) →
      (∀ j, famGraph (χ j) ∈ S.Ω F1 D1 (p + m + 1)) →
      famGraph (fun l z => f l (fun j => χ j l z)) ∈
        S.Ω (F0 + F1 + a) (D0 + (p + m) * D1 + c) (p + m + 1) := by
  obtain ⟨C₁, C₂, hC⟩ := graphOf_comp_exp S (p + m)
  refine ⟨(p + m + 1) + C₁, (p + m) + C₂, ?_⟩
  intro F0 F1 D0 D1 f χ hf hχ
  have hcoord : ∀ j : Fin (p + m),
      graphOf (fun x : Fin (p + m) → ℝ => flatChart χ x j) ∈
        S.Ω (F1 + (p + m + 1)) (D1 + 1) (p + m + 1) := by
    intro j
    induction j using Fin.addCases with
    | left i =>
        rw [graphOf_flatChart_castAdd]
        exact Omega.mono (graphOf_coord_mem S (Fin.castAdd m i)) (by omega) (by omega)
    | right k =>
        rw [graphOf_flatChart_natAdd]
        exact Omega.mono (hχ k) (by omega) (by omega)
  have hmain := hC F0 (F1 + (p + m + 1)) D0 (D1 + 1) (flatFun f) (flatChart χ)
    hf hcoord
  rw [famGraph_eq_graphOf_flatFun, flatFun_comp]
  refine Omega.mono hmain (by omega) ?_
  rw [Nat.mul_succ]
  omega

/-! ## 5. Polynomial bookkeeping -/

theorem eval_eval₂_C_nat {σ τ : Type*} (x : τ → ℕ) (g : σ → MvPolynomial τ ℕ)
    (q : MvPolynomial σ ℕ) :
    MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C g q)
      = MvPolynomial.eval (fun s => MvPolynomial.eval x (g s)) q := by
  rw [MvPolynomial.eval_eval₂,
    show (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℕ from
      RingHom.ext (fun a => by simp)]
  rfl

theorem eval_eval₂_C_real {σ τ : Type*} (x : τ → ℝ) (g : σ → MvPolynomial τ ℝ)
    (q : MvPolynomial σ ℝ) :
    MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C g q)
      = MvPolynomial.eval (fun s => MvPolynomial.eval x (g s)) q := by
  rw [MvPolynomial.eval_eval₂,
    show (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℝ from
      RingHom.ext (fun a => by simp)]
  rfl

theorem eval₂_natCast_comp {σ : Type*} (v : σ → ℕ) (p : MvPolynomial σ ℕ) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun i => (v i : ℝ)) p
      = ((MvPolynomial.eval v p : ℕ) : ℝ) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [MvPolynomial.eval₂_add, hp, hq, MvPolynomial.eval_add, Nat.cast_add]
  | mul_X p i hp =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, hp, Nat.cast_mul]


end

end Work.WilkG4c
