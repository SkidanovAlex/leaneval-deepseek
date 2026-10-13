import Mathlib
import Submission.Work.WilG4c.Clean.EngineFibre
import Submission.Work.WilG4c.PerLambda.ChartsOK_extends
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.Clean.LipR0Aux1
import Submission.Work.WilG4c.FibreSmoothThin
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilG0.Subst
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

/-! ## 1. Elementary helpers

The assembly below needs a handful of lemmas that are not yet in the area:

* `paramSet_mem`: the *parameter set* `Λ_κ = {l | ∃ y, Fin.append l y ∈ κ}` of a cell is
  `Ω`-bounded, at the same degree, for a format cost independent of the cell;
* `clean_graphOf_const_mem`: a constant graph is `Ω`-bounded with format `m+1` and degree `1`;
* `ChartsOK_extends'`: the per-parameter extension of a chart family by a constant, needed only
  on `Λ ∩ Λ'` (variant of `Work.WilkG4c.PerLambda.ChartsOK_extends`);
* `fibreSmooth_of_not_mem'`, `escape_of_interior_empty'`: the two geometric interfaces of
  `Submission/Work/WilG4c/StepCleanAsm.lean`, restated for a *family* of core sets;
* the polynomial bookkeeping `exists_poly_eval_poly`, `exists_poly_shift2` for the final degree. -/

/-- The parameter set `Λ_κ = {l | ∃ y, Fin.append l y ∈ κ}` of an `Ω`-bounded set is
`Ω`-bounded, at the *same* degree, for a format cost `K` depending only on `p` and `N`.  This is
the iterated projection of the cell (`SOMin.proj`), where the fibre coordinates are glued on the
right with `Fin.append`. -/
theorem paramSet_mem (S : SOMin) (p N : ℕ) : ∃ K : ℕ,
    ∀ (F D : ℕ) (κ : Set (Fin (p + N) → ℝ)), κ ∈ S.Ω F D (p + N) →
      {l : Fin p → ℝ | ∃ y : Fin N → ℝ, Fin.append l y ∈ κ} ∈ S.Ω (F + K) D p := by
  induction N with
  | zero =>
    refine ⟨0, fun F D κ hκ => ?_⟩
    have hset : {l : Fin p → ℝ | ∃ y : Fin 0 → ℝ, Fin.append l y ∈ κ} = κ := by
      ext l
      constructor
      · rintro ⟨y, hy⟩
        have hyl : Fin.append l y = l := by
          funext i
          simpa using Fin.append_left l y i
        rwa [hyl] at hy
      · intro hl
        refine ⟨Fin.elim0, ?_⟩
        have hyl : Fin.append l (Fin.elim0 : Fin 0 → ℝ) = l := by
          funext i
          simpa using Fin.append_left l (Fin.elim0 : Fin 0 → ℝ) i
        rwa [hyl]
    rw [hset]
    exact hκ
  | succ N ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨K + (N + p + 2), fun F D κ hκ => ?_⟩
    have h := hK (F + 1) D (projLast κ) (S.proj hκ)
    have hset : {l : Fin p → ℝ | ∃ y : Fin N → ℝ, Fin.append l y ∈ projLast κ}
        = {l : Fin p → ℝ | ∃ y : Fin (N + 1) → ℝ, Fin.append l y ∈ κ} := by
      ext l
      constructor
      · rintro ⟨w, t, ht⟩
        refine ⟨Fin.snoc w t, ?_⟩
        rwa [Fin.append_snoc]
      · rintro ⟨y, hy⟩
        refine ⟨Fin.init y, y (Fin.last N), ?_⟩
        have h1 : Fin.append l y = Fin.snoc (Fin.append l (Fin.init y)) (y (Fin.last N)) := by
          conv_lhs => rw [← Fin.snoc_init_self y]
          exact Fin.append_snoc l (Fin.init y) (y (Fin.last N))
        rw [← h1]
        exact hy
    rw [← hset]
    refine Work.WilG1.Omega.mono h (by omega) le_rfl

/-- A constant graph is `Ω`-bounded with format `m + 1` and degree `1`. -/
theorem clean_graphOf_const_mem (S : SOMin) (m : ℕ) (c : ℝ) :
    graphOf (fun _ : Fin m → ℝ => c) ∈ S.Ω (m + 1) 1 (m + 1) := by
  have h := S.hyp (m + 1)
    ((MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) ℝ) - MvPolynomial.C c)
  have hset : {z : Fin (m + 1) → ℝ | MvPolynomial.eval z
      ((MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) ℝ) - MvPolynomial.C c) = 0}
      = graphOf (fun _ : Fin m → ℝ => c) := by
    ext z
    simp only [Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C, graphOf, sub_eq_zero]
  rw [hset] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
  · exact Work.WilG5.td_X_le (Fin.last m)
  · exact le_trans (Work.WilG5.td_C_le c) (by omega)

/-- **Extension of a chart family off a parameter set.**  If the charts of `Φ` are good on
`Λ ∩ Λ'` (i.e. on the parameters that really belong to the cell) and are replaced by the
constant `c ∈ openCube n` on the complement of `Λ'`, then the resulting family still satisfies
`ChartsOK` (over all of `Λ`).  This is `Work.WilkG4c.PerLambda.ChartsOK_extends` with the
"good on `Λ'`" hypothesis weakened to "good on `Λ ∩ Λ'`", which is what the per-cell application
of the engine supplies. -/
theorem ChartsOK_extends' {S : SOMin} {p n k a Dg r : ℕ} {Λ Λ' : Set (Fin p → ℝ)}
    {F : Family k p n} {Φ : Finset (ChartTuple p n)} {c : Fin n → ℝ}
    (hc : c ∈ openCube n) (hval : ValuesIn01 Λ F)
    (mod : ChartTuple p n → ChartTuple p n)
    (hmod : ∀ φ j l, l ∈ Λ' → ∀ t : Fin n → ℝ, mod φ j l t = φ j l t)
    (hmodc : ∀ φ j l, l ∉ Λ' → ∀ t : Fin n → ℝ, mod φ j l t = c j)
    (hΩ : ∀ φ ∈ Φ, ∀ j : Fin n, famGraph ((mod φ) j) ∈ S.Ω a Dg (p + n + 1))
    (h : ∀ φ ∈ Φ, ∀ l, l ∈ Λ → l ∈ Λ' →
      (∀ t ∈ openCube n, (fun j => φ j l t) ∈ openCube n) ∧
      ∀ i, ContDiffOn ℝ r (fun t => F i l (fun j => φ j l t)) (openCube n) ∧
        ∀ m, m ≤ r → ∀ t ∈ openCube n,
          ‖iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t‖ ≤ 1) :
    ∃ Φ' : Finset (ChartTuple p n), (∀ φ ∈ Φ, mod φ ∈ Φ') ∧ Φ'.card ≤ Φ.card ∧
      ChartsOK S a Dg r Λ F Φ' := by
  refine ⟨Φ.image mod, fun φ hφ => Finset.mem_image_of_mem mod hφ, Finset.card_image_le, ?_⟩
  intro φ' hφ'
  obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hφ'
  refine ⟨fun j => hΩ φ hφ j, ?_⟩
  intro l hl
  by_cases hl' : l ∈ Λ'
  · obtain ⟨hcube, hrest⟩ := h φ hφ l hl hl'
    have hpt : ∀ t : Fin n → ℝ, (fun j => mod φ j l t) = (fun j => φ j l t) :=
      fun t => funext (fun j => hmod φ j l hl' t)
    have hfun : ∀ i, (fun t : Fin n → ℝ => F i l (fun j => mod φ j l t))
        = (fun t : Fin n → ℝ => F i l (fun j => φ j l t)) :=
      fun i => funext (fun t => by rw [hpt t])
    refine ⟨fun t ht => by rw [hpt t]; exact hcube t ht, ?_⟩
    intro i
    refine ⟨?_, ?_⟩
    · rw [hfun i]; exact (hrest i).1
    · intro m hm t ht
      rw [hfun i]; exact (hrest i).2 m hm t ht
  · have hconst : ∀ t : Fin n → ℝ, (fun j => mod φ j l t) = c :=
      fun t => funext (fun j => hmodc φ j l hl' t)
    refine ⟨fun t ht => by rw [hconst t]; exact hc, ?_⟩
    intro i
    have hfun : (fun t : Fin n → ℝ => F i l (fun j => mod φ j l t))
        = (fun _ : Fin n → ℝ => F i l c) := funext (fun t => by rw [hconst t])
    constructor
    · rw [hfun]; exact contDiffOn_const
    · intro m hm t ht
      rw [hfun]
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (hval i l hl c hc).1]
        exact le_of_lt (hval i l hl c hc).2
      · rw [iteratedFDeriv_const_of_ne (ne_of_gt hpos) (F i l c)]
        simp

/-- A point outside every core set is fibre-smooth with unit fibre norms. -/
theorem fibreSmooth_of_not_mem' {p N k r : ℕ} {F : Family k p N} (hDef : NormLeOneDef F r)
    {Wf : Fin k → Set (Fin (p + N) → ℝ)} {l : Fin p → ℝ} {y : Fin N → ℝ}
    (hy : y ∈ openCube N)
    (hcov : ∀ i : Fin k, {z : Fin N → ℝ | ¬ ContDiffAt ℝ r (F i l) z} ⊆
      {z : Fin N → ℝ | Fin.append l z ∈ Wf i})
    (hnot : ∀ i : Fin k, Fin.append l y ∉ Wf i) :
    ∀ i : Fin k, ContDiffAt ℝ r (F i l) y ∧
      ∀ m, m ≤ r → ‖iteratedFDeriv ℝ m (F i l) y‖ ≤ 1 := by
  intro i
  have hsmooth : ContDiffAt ℝ r (F i l) y := by
    by_contra hc
    exact hnot i (hcov i hc)
  exact ⟨hsmooth, fun m hm => hDef i l y hy hsmooth m hm⟩

/-- Escape in the fibre: from the empty interior of a fibre of a set, every cube point is
arbitrarily close, *at the same parameter*, to a cube point outside the set. -/
theorem escape_of_interior_empty' {p N : ℕ} {Z : Set (Fin (p + N) → ℝ)} {l : Fin p → ℝ}
    (hZ : interior {z : Fin N → ℝ | Fin.append l z ∈ Z} = ∅)
    {x : Fin N → ℝ} (hx : x ∈ openCube N) {η : ℝ} (hη : 0 < η) :
    ∃ y ∈ openCube N, dist y x < η ∧ Fin.append l y ∉ Z := by
  by_contra hcon
  push_neg at hcon
  have hne : (openCube N ∩ Metric.ball x η).Nonempty :=
    ⟨x, hx, by rw [Metric.mem_ball, dist_self]; exact hη⟩
  have hopen : IsOpen (openCube N ∩ Metric.ball x η) :=
    (openCube_isOpen' N).inter Metric.isOpen_ball
  have hsub : openCube N ∩ Metric.ball x η ⊆ {z : Fin N → ℝ | Fin.append l z ∈ Z} :=
    fun z hz => hcon z hz.1 (Metric.mem_ball.mp hz.2)
  have hle : openCube N ∩ Metric.ball x η
      ⊆ interior {z : Fin N → ℝ | Fin.append l z ∈ Z} := interior_maximal hsub hopen
  rw [hZ] at hle
  exact Set.not_nonempty_empty (hne.mono (fun z hz => hle hz))

/-! ## 2. Polynomial bookkeeping for the final degree -/

/-- Evaluation of `Polynomial.eval₂ C X` at `![x, 1]` recovers `c.eval x`. -/
theorem eval_polyToMv (c : Polynomial ℕ) (x : ℕ) :
    MvPolynomial.eval ![x, 1] (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) c)
      = c.eval x := by
  have hcomp : (MvPolynomial.eval (fun i : Fin 2 => ![x, 1] i)).comp
      (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
      = Polynomial.eval₂RingHom (RingHom.id ℕ) x := by
    refine Polynomial.ringHom_ext ?_ ?_
    · intro a; simp [Polynomial.eval₂RingHom]
    · simp [Polynomial.eval₂RingHom]
  exact RingHom.congr_fun hcomp c

/-- `c.eval (eval (D,r) B₀) + K` is dominated by the evaluation of a fixed polynomial. -/
theorem exists_poly_eval_poly (c : Polynomial ℕ) (B₀ : MvPolynomial (Fin 2) ℕ) (K : ℕ) :
    ∃ B : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      c.eval (MvPolynomial.eval ![D, r] B₀) + K ≤ MvPolynomial.eval ![D, r] B := by
  set pc : MvPolynomial (Fin 2) ℕ := Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) c
    with hpc
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 2 =>
    if i = 0 then B₀ else MvPolynomial.C 1) pc + MvPolynomial.C K, ?_⟩
  intro D r
  have h1 : MvPolynomial.eval ![D, r] (MvPolynomial.bind₁ (fun i : Fin 2 =>
      if i = 0 then B₀ else MvPolynomial.C 1) pc) = c.eval (MvPolynomial.eval ![D, r] B₀) := by
    have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, r]
      (fun i : Fin 2 => if i = 0 then B₀ else MvPolynomial.C 1) pc
    have hfun : (fun i : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
        (if i = 0 then B₀ else MvPolynomial.C 1))
        = ![MvPolynomial.eval ![D, r] B₀, 1] := by
      funext i; fin_cases i <;> simp
    rw [hfun] at h
    have h2 : (MvPolynomial.eval₂Hom (RingHom.id ℕ) ![MvPolynomial.eval ![D, r] B₀, 1]) pc
        = c.eval (MvPolynomial.eval ![D, r] B₀) := by
      simpa using eval_polyToMv c (MvPolynomial.eval ![D, r] B₀)
    rw [h2] at h
    exact h
  rw [MvPolynomial.eval_add, h1, MvPolynomial.eval_C]

/-- The degree substitution `X₀ ↦ X₀ + B₁ + K` on a two-variable polynomial. -/
theorem exists_poly_shift2 (b B₁ : MvPolynomial (Fin 2) ℕ) (K : ℕ) :
    ∃ B : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![D + MvPolynomial.eval ![D, r] B₁ + K, r] b
        ≤ MvPolynomial.eval ![D, r] B := by
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X 0 + B₁ + MvPolynomial.C K else MvPolynomial.X 1) b, ?_⟩
  intro D r
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, r]
    (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 + B₁ + MvPolynomial.C K
      else MvPolynomial.X 1) b
  have hfun : (fun i : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
      (if i = 0 then MvPolynomial.X 0 + B₁ + MvPolynomial.C K else MvPolynomial.X 1))
      = ![D + MvPolynomial.eval ![D, r] B₁ + K, r] := by
    funext i
    fin_cases i
    · show MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
        (MvPolynomial.X 0 + B₁ + MvPolynomial.C K) = D + MvPolynomial.eval ![D, r] B₁ + K
      simp
    · show MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r] (MvPolynomial.X 1) = r
      simp
  rw [hfun] at h
  exact le_of_eq h.symm


end Work.WilG4c
