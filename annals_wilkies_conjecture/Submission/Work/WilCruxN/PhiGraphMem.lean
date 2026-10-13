import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilCrux.flatGraphMem
import Submission.Work.WilG4c.EpsFDerivSetMem
import Submission.Work.WilG4c.FDerivDirGraphMem
import Submission.Work.WilG4a.affine_comb_graph_mem
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG4b.projCoords_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilCruxN

open WilkiesDesign

/-! ## Elementary facts about `Fin.append` -/

/-- `Fin.append` of the two coordinate blocks of `u` is `u`. -/
theorem append_comp_eq_self {a b : ℕ} (u : Fin (a + b) → ℝ) :
    Fin.append (fun i : Fin a => u (Fin.castAdd b i))
      (fun j : Fin b => u (Fin.natAdd a j)) = u := by
  funext k
  refine Fin.addCases (motive := fun k => Fin.append (fun i : Fin a => u (Fin.castAdd b i))
      (fun j : Fin b => u (Fin.natAdd a j)) k = u k) ?_ ?_ k
  · intro i; rw [Fin.append_left]
  · intro j; rw [Fin.append_right]

/-- Elementary degree bookkeeping: `p.eval D ≤ (p + q).eval D`. -/
theorem eval_le_add_right (D : ℕ) (p q : Polynomial ℕ) : p.eval D ≤ (p + q).eval D := by
  rw [Polynomial.eval_add]; exact Nat.le_add_right _ _

/-- Elementary degree bookkeeping: `q.eval D ≤ (p + q).eval D`. -/
theorem eval_le_add_left (D : ℕ) (p q : Polynomial ℕ) : q.eval D ≤ (p + q).eval D := by
  rw [Polynomial.eval_add]; exact Nat.le_add_left _ _

/-! ## The directional-derivative graph, with polynomial bookkeeping -/

/-- `EpsFDerivSetMem` composed with `FDerivDirGraphMem`: the graph of the total directional
derivative `w ↦ fderiv ℝ φ w e` is `Ω`-definable with a format independent of the degree
parameter `D` and a degree which is a polynomial in `D`. -/
theorem dirGraphMem_poly (S : WilkiesDesign.SOMin) (N F : ℕ) (e : Fin N → ℝ) :
    ∃ (A : ℕ) (c : Polynomial ℕ), ∀ (D : ℕ) (φ : (Fin N → ℝ) → ℝ),
      WilkiesDesign.graphOf φ ∈ S.Ω F D (N + 1) →
      WilkiesDesign.graphOf (fun w : Fin N → ℝ => fderiv ℝ φ w e) ∈
        S.Ω A (c.eval D) (N + 1) := by
  obtain ⟨Ae, be, hEps⟩ := Work.WilG4c.EpsFDerivSetMem S N F
  obtain ⟨K, m, cc, hFDG⟩ := Work.WilG4c.FDerivDirGraphMem S N e
  exact ⟨Ae + K, Polynomial.C m * be + Polynomial.C cc,
    fun D φ hφ => hFDG Ae be D φ (hEps D φ hφ)⟩

/-! ## The difference of two graphs, with polynomial bookkeeping -/

/-- `affine_comb_graph_mem` in the form `f - h`: if the graphs of `f` and `h` are
`Ω`-definable at degree `D`, then the graph of `f - h` is `Ω`-definable at a format
independent of `D` and a degree polynomial in `D`. -/
theorem subGraphMem_poly (S : WilkiesDesign.SOMin) (n F₁ F₂ : ℕ) :
    ∃ (A : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (f h : (Fin n → ℝ) → ℝ),
      WilkiesDesign.graphOf f ∈ S.Ω F₁ D (n + 1) →
      WilkiesDesign.graphOf h ∈ S.Ω F₂ D (n + 1) →
      WilkiesDesign.graphOf (fun z : Fin n → ℝ => f z - h z) ∈ S.Ω A (b.eval D) (n + 1) := by
  obtain ⟨a, b, hb⟩ := Work.WilG4a.affine_comb_graph_mem S n (max F₁ F₂)
  refine ⟨a, Work.WilG1.psubst b 1, ?_⟩
  intro D f h hf hh
  have hf' : WilkiesDesign.graphOf f ∈ S.Ω (max F₁ F₂) D (n + 1) :=
    Work.WilG5.mem_mono hf (max F₁ F₂) D (le_max_left _ _) le_rfl
  have hh' : WilkiesDesign.graphOf h ∈ S.Ω (max F₁ F₂) D (n + 1) :=
    Work.WilG5.mem_mono hh (max F₁ F₂) D (le_max_right _ _) le_rfl
  have hres := hb D 1 hf' hh' (0 : ℝ) 1 (-1)
  have hfun : (fun z : Fin n → ℝ => (0 : ℝ) + 1 * f z + (-1) * h z) =
      (fun z : Fin n → ℝ => f z - h z) := by
    funext z; ring
  rw [hfun] at hres
  simpa only [Work.WilG1.eval_psubst] using hres

/-! ## Coordinate lift of a graph along a polynomial degree bound -/

/-- `coordPre_mem` with the degree tracked as a polynomial: if `A` is `Ω`-definable at degree
`b.eval D`, then `coordPre ι A` is `Ω`-definable at a format independent of `D` (given the
format of `A`) and degree `(b + C k).eval D`. -/
theorem coordPre_mem_poly {m N : ℕ} (S : WilkiesDesign.SOMin) {F : ℕ} {ι : Fin m → Fin N}
    {A : Set (Fin m → ℝ)} {b : Polynomial ℕ} {D : ℕ} (h : A ∈ S.Ω F (b.eval D) m) :
    Work.WilG5.coordPre ι A ∈
      S.Ω (F + 64 * (N + m) + 64) ((b + Polynomial.C (32 * (N + m) + 32)).eval D) N := by
  have hc := Work.WilG5.coordPre_mem (S := S) (N := N) (D := b.eval D) (A := A) (ι := ι) h
  have hdeg : b.eval D + 32 * (N + m) + 32 =
      (b + Polynomial.C (32 * (N + m) + 32)).eval D := by
    rw [Polynomial.eval_add, Polynomial.eval_C]
    omega
  rw [hdeg] at hc
  exact hc

/-! ## Fibre-constant functions -/

/-- The coordinate selection `Fin (a+1) → Fin (a+b+1)` keeping the `a` parameter coordinates
and the value coordinate, and forgetting the `b` fibre coordinates. -/
def parSel (a b : ℕ) : Fin (a + 1) → Fin (a + b + 1) :=
  Fin.lastCases (Fin.last (a + b)) (fun i : Fin a => Fin.castAdd (b + 1) i)

theorem parSel_last (a b : ℕ) : parSel a b (Fin.last a) = Fin.last (a + b) :=
  Fin.lastCases_last ..

theorem parSel_castSucc (a b : ℕ) (i : Fin a) :
    parSel a b (Fin.castSucc i) = Fin.castAdd (b + 1) i :=
  Fin.lastCases_castSucc i

/-- The graph of a function on `ℝ^{a+b}` which only depends on the `a` parameter coordinates
is the coordinate preimage of the graph of its parameter part. -/
theorem graphOf_fibreConst_eq (a b : ℕ) (pt : (Fin a → ℝ) → ℝ) :
    WilkiesDesign.graphOf (fun u : Fin (a + b) → ℝ => pt (u ∘ Fin.castAdd b))
      = Work.WilG5.coordPre (parSel a b) (WilkiesDesign.graphOf pt) := by
  ext x
  simp only [WilkiesDesign.graphOf, Work.WilG5.coordPre, Set.mem_ofPred_eq, Function.comp_apply]
  have hlast : parSel a b (Fin.last a) = Fin.last (a + b) := parSel_last a b
  have hinit : Fin.init (x ∘ parSel a b) = Fin.init x ∘ Fin.castAdd b := by
    funext i
    show x (parSel a b i.castSucc) = x ((Fin.castAdd b i).castSucc)
    rw [parSel_castSucc]
    congr 1
  rw [hlast, hinit]

/-! ## The flat sheet, with polynomial bookkeeping -/

/-- **The flat sheet of a definable family is definable, with tracked degree.**
This is `Work.WilCrux.flatGraphMem` with the degree bound exhibited as a polynomial in the
degree parameter `D`: the proof is the same, and the only difference is that the projection
`Work.WilG4b.projCoords_mem` is applied at the (tracked) degree `D + (fibreP a b).totalDegree`
and the resulting linear polynomial `p` is pre-composed with `X + C (fibreP a b).totalDegree`. -/
theorem flatGraphMem_poly (S : WilkiesDesign.SOMin) {a b F : ℕ} :
    ∃ (A : ℕ) (c : Polynomial ℕ),
      ∀ (D : ℕ) (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1) →
        WilkiesDesign.graphOf (fun w : Fin a → ℝ => G w 0) ∈ S.Ω A (c.eval D) (a + 1) := by
  obtain ⟨K, p, hp⟩ := Work.WilG4b.projCoords_mem S (Work.WilCrux.flatE a b)
  refine ⟨(max F (a + b + 1) + 1) + K,
    p.comp (Polynomial.X + Polynomial.C (Work.WilCrux.fibreP a b).totalDegree), ?_⟩
  intro D G hG
  set Z : Set (Fin (a + b + 1) → ℝ) :=
    {u | MvPolynomial.eval u (Work.WilCrux.fibreP a b) = 0} with hZdef
  have hZ : Z ∈ S.Ω (a + b + 1) (Work.WilCrux.fibreP a b).totalDegree (a + b + 1) := by
    rw [hZdef]; exact S.hyp (a + b + 1) (Work.WilCrux.fibreP a b)
  have hG' : WilkiesDesign.CG.famGraph G ∈ S.Ω (max F (a + b + 1)) D (a + b + 1) :=
    Work.WilG4a.mem_mono hG (le_max_left _ _) le_rfl
  have hZ' : Z ∈ S.Ω (max F (a + b + 1)) (Work.WilCrux.fibreP a b).totalDegree
      (a + b + 1) :=
    Work.WilG4a.mem_mono hZ (le_max_right _ _) le_rfl
  have hX : (WilkiesDesign.CG.famGraph G ∩ Z) ∈
      S.Ω (max F (a + b + 1) + 1) (D + (Work.WilCrux.fibreP a b).totalDegree)
        (a + b + 1) := by
    have h := S.inter (F := max F (a + b + 1))
        (fun i : Fin 2 => if i = 0 then D else (Work.WilCrux.fibreP a b).totalDegree)
        (fun i : Fin 2 => if i = 0 then WilkiesDesign.CG.famGraph G else Z)
        (by intro i
            fin_cases i
            · simpa using hG'
            · simpa using hZ')
    rw [show (∑ i : Fin 2, (if i = 0 then D else (Work.WilCrux.fibreP a b).totalDegree))
        = D + (Work.WilCrux.fibreP a b).totalDegree from by
      rw [Fin.sum_univ_two]; norm_num] at h
    rwa [Work.WilG4a.iInter_fin_two (WilkiesDesign.CG.famGraph G) Z] at h
  have himg := hp (max F (a + b + 1) + 1) (D + (Work.WilCrux.fibreP a b).totalDegree)
    (WilkiesDesign.CG.famGraph G ∩ Z) hX
  rw [← Work.WilCrux.coordImage_eq (a := a) (b := b) G]
  rw [hZdef] at himg
  rw [show (p.comp (Polynomial.X +
        Polynomial.C (Work.WilCrux.fibreP a b).totalDegree)).eval D
      = p.eval (D + (Work.WilCrux.fibreP a b).totalDegree) from by
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]]
  exact himg

/-! ## The main lemma -/

/-- **Ω-definability of the graph of the parameter-partial difference.**

Ported from `Work.WilCrux.PhiGraphMem` (`Submission/Work/WilCrux/PhiGraphMem.lean`), whose proof
body is complete but calls `Work.WilCrux.PhiSliceZeroMem`, a `sorry` stub.  Here the "flat graph"
input must be re-done *with polynomial degree tracking*: the statement

  `∃ A c, ∀ D G, famGraph G ∈ S.Ω F D (a+b+1) → graphOf (fun w => G w 0) ∈ S.Ω A (c.eval D) (a+1)`

is provable by adapting the *proven*, `sorry`-free `Work.WilCrux.flatGraphMem`
(`Submission/Work/WilCrux/flatGraphMem.lean`), which gives the same conclusion with the bounds
merely existential (`∃ F' D'`).  Its proof exhibits the degree explicitly as
`p.eval (D + (fibreP a b).totalDegree)` for a fixed polynomial `p` coming from
`Work.WilG4b.projCoords_mem`, so the polynomial-tracked version follows with
`Polynomial.eval_comp` and `Polynomial.eval_add` (take `c := p.comp (X + C (fibreP a b).totalDegree)`).

Then port the `PhiGraphMem` proof body verbatim from `Submission/Work/WilCrux/PhiGraphMem.lean`
(it uses `dirGraphMem_poly` from `Work.WilG4c.EpsFDerivSetMem`/`Work.WilG4c.FDerivDirGraphMem`,
`subGraphMem_poly` from `Work.WilG4a.affine_comb_graph_mem`, `coordPre_mem_poly` from
`Work.WilG5.coordPre_mem`, and `graphOf_fibreConst_eq` / `parSel` — all of which are also in that
file and are `sorry`-free; you may copy them into your own module).

Read `Submission/Work/WilCrux/PhiGraphMem.lean`, `Submission/Work/WilCrux/flatGraphMem.lean` and
the stub `Submission/Work/WilCrux/PhiSliceZeroMem.lean`.  Do NOT use any declaration whose
`#print axioms` mentions `sorryAx` (in particular not `Work.WilCrux.PhiSliceZeroMem` nor
`Work.WilCrux.PhiGraphMem`). -/
theorem PhiGraphMem (S : WilkiesDesign.SOMin) {a b F : ℕ} :
    ∃ (A : ℕ) (c : Polynomial ℕ), ∀ (D : ℕ)
      (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a),
      WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1) →
      WilkiesDesign.CG.famGraph (fun (w : Fin a → ℝ) (z : Fin b → ℝ) =>
          fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)
              (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
            - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w (Pi.single i 1))
        ∈ S.Ω A (c.eval D) (a + b + 1) := by
  classical
  have key : ∀ i : Fin a, ∃ (A : ℕ) (c : Polynomial ℕ), ∀ (D : ℕ)
        (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1) →
      WilkiesDesign.CG.famGraph (fun (w : Fin a → ℝ) (z : Fin b → ℝ) =>
          fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)
              (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
            - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w (Pi.single i 1))
        ∈ S.Ω A (c.eval D) (a + b + 1) := by
    intro i
    obtain ⟨A1, c1, hDir1⟩ := dirGraphMem_poly S (a + b) F
      (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
    obtain ⟨A2, c2, hSlice⟩ := flatGraphMem_poly (S := S) (a := a) (b := b) (F := F)
    obtain ⟨A3, c3, hDir2⟩ := dirGraphMem_poly S a A2 (Pi.single i 1)
    let e2 : Polynomial ℕ := c3.comp c2 + Polynomial.C (32 * ((a + b + 1) + (a + 1)) + 32)
    let F₂ : ℕ := A3 + 64 * ((a + b + 1) + (a + 1)) + 64
    obtain ⟨Asub, bsub, hSub'⟩ := subGraphMem_poly S (a + b) A1 F₂
    refine ⟨Asub, bsub.comp (c1 + e2), ?_⟩
    intro D G hG
    have hG1 : WilkiesDesign.graphOf (Work.WilG4c.famFun G) ∈ S.Ω F D (a + b + 1) := by
      rw [Work.WilG4c.graphOf_famFun]; exact hG
    have hQ := hDir1 D (Work.WilG4c.famFun G) hG1
    have hSlice' : WilkiesDesign.graphOf
        (fun w : Fin a → ℝ => G w (0 : Fin b → ℝ)) ∈ S.Ω A2 (c2.eval D) (a + 1) :=
      hSlice D G hG
    have hU : WilkiesDesign.graphOf (fun w : Fin a → ℝ =>
        fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w (Pi.single i 1)) ∈
        S.Ω A3 ((c3.comp c2).eval D) (a + 1) := by
      have h := hDir2 (c2.eval D) (fun w : Fin a → ℝ => G w (0 : Fin b → ℝ)) hSlice'
      rwa [← Polynomial.eval_comp] at h
    have hU4 : WilkiesDesign.graphOf (fun u : Fin (a + b) → ℝ =>
        fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (u ∘ Fin.castAdd b) (Pi.single i 1)) ∈
        S.Ω F₂ (e2.eval D) (a + b + 1) := by
      rw [graphOf_fibreConst_eq (a := a) (b := b)
        (pt := fun w : Fin a → ℝ => fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w (Pi.single i 1))]
      exact coordPre_mem_poly (S := S) hU
    have hQ' : WilkiesDesign.graphOf (fun u : Fin (a + b) → ℝ =>
        fderiv ℝ (Work.WilG4c.famFun G) u (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))) ∈
        S.Ω A1 ((c1 + e2).eval D) (a + b + 1) :=
      Work.WilG5.mem_mono hQ A1 _ le_rfl (eval_le_add_right D c1 e2)
    have hU4' : WilkiesDesign.graphOf (fun u : Fin (a + b) → ℝ =>
        fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (u ∘ Fin.castAdd b) (Pi.single i 1)) ∈
        S.Ω F₂ ((c1 + e2).eval D) (a + b + 1) :=
      Work.WilG5.mem_mono hU4 _ _ le_rfl (eval_le_add_left D c1 e2)
    have hres := hSub' ((c1 + e2).eval D)
      (fun u : Fin (a + b) → ℝ =>
        fderiv ℝ (Work.WilG4c.famFun G) u (Fin.append (Pi.single i 1) (0 : Fin b → ℝ)))
      (fun u : Fin (a + b) → ℝ =>
        fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (u ∘ Fin.castAdd b) (Pi.single i 1))
      hQ' hU4'
    have hfin : WilkiesDesign.graphOf (fun z : Fin (a + b) → ℝ =>
        fderiv ℝ (Work.WilG4c.famFun G) z (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
          - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (z ∘ Fin.castAdd b) (Pi.single i 1)) ∈
        S.Ω Asub ((bsub.comp (c1 + e2)).eval D) (a + b + 1) := by
      rw [Polynomial.eval_comp]
      exact hres
    have hfun : (fun z : Fin (a + b) → ℝ =>
        fderiv ℝ (Work.WilG4c.famFun G) z (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
          - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (z ∘ Fin.castAdd b) (Pi.single i 1))
        = Work.WilG4c.famFun (fun (w : Fin a → ℝ) (z : Fin b → ℝ) =>
          fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)
              (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
            - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w (Pi.single i 1)) := by
      funext u
      simp only [Work.WilG4c.famFun, Function.comp_def]
      rw [append_comp_eq_self u]
    rw [hfun, Work.WilG4c.graphOf_famFun] at hfin
    exact hfin
  choose A c hAc using key
  refine ⟨Finset.univ.sup A, ∑ i : Fin a, c i, ?_⟩
  intro D G i hG
  have h := hAc i D G hG
  refine Work.WilG5.mem_mono h (Finset.univ.sup A) ((∑ j : Fin a, c j).eval D) ?_ ?_
  · exact Finset.le_sup (Finset.mem_univ i)
  · simpa only [Polynomial.eval_finsetSum] using
      Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin a => (c j).eval D)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

end Work.WilCruxN
