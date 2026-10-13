import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG1.Main
import Submission.Work.WilG4c.BadLocusThin
import Submission.Work.WilG4b.projCoords_mem
import Submission.Work.WilCruxN.SliceDerivJointNorm
import Submission.Work.WilCruxN.ParamDerivJointClean
import Submission.Work.WilCrux.C1Assembly

set_option maxHeartbeats 1000000

namespace Work.WilCruxN

open Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-! ## The flat sheet of a definable family is definable

If the graph of the family `G : ℝ^a → ℝ^b → ℝ` is an `Ω`-set, then so is the graph of the
flat-sheet function `w ↦ G w 0`.  The joint set `famGraph G ∩ {z = 0}` projects (along the
coordinate map that reads the `a` parameter coordinates and the value coordinate) onto exactly
that graph, and `Work.WilG4b.projCoords_mem` makes the coordinate image `Ω`-definable. -/

/-- The coordinate map reading the parameter coordinates and the value coordinate of
`ℝ^{a+b+1}`: `i ↦ i` for `i : Fin a` and `Fin.last a ↦ Fin.last (a+b)`. -/
private def flatE (a b : ℕ) : Fin (a+1) → Fin (a+b+1) :=
  Fin.append (fun i : Fin a => Fin.castAdd (b+1) i) (fun _ : Fin 1 => Fin.last (a+b))

private theorem flatE_castAdd (a b : ℕ) (i : Fin a) :
    flatE a b (Fin.castAdd 1 i) = Fin.castAdd (b+1) i :=
  Fin.append_left (fun i : Fin a => Fin.castAdd (b+1) i) (fun _ : Fin 1 => Fin.last (a+b)) i

private theorem flatE_last (a b : ℕ) : flatE a b (Fin.last a) = Fin.last (a+b) := by
  have h : (Fin.last a : Fin (a+1)) = Fin.natAdd a (0 : Fin 1) := by
    ext; simp [Fin.last, Fin.natAdd]
  rw [h]
  exact Fin.append_right (fun i : Fin a => Fin.castAdd (b+1) i)
    (fun _ : Fin 1 => Fin.last (a+b)) 0

/-- A coordinate hyperplane is `Ω`-definable. -/
private theorem coordZero_mem (S : WilkiesDesign.SOMin) {n : ℕ} (D : ℕ) (k : Fin n) :
    {x : Fin n → ℝ | x k = 0} ∈ S.Ω n ((Polynomial.C 1).eval D) n := by
  have h := Work.WilG1.Omega.hyp_mem (S := S) D (MvPolynomial.X k : MvPolynomial (Fin n) ℝ)
  have hset : {x : Fin n → ℝ |
      MvPolynomial.eval x (MvPolynomial.X k : MvPolynomial (Fin n) ℝ) = 0}
      = {x : Fin n → ℝ | x k = 0} := by
    ext x; simp
  rw [hset] at h
  exact Work.WilG1.Omega.mono h le_rfl (by simp [MvPolynomial.totalDegree_X])

/-- The fibre block `z = 0` is `Ω`-definable. -/
private theorem zeroFibre_mem (S : WilkiesDesign.SOMin) (a b D : ℕ) :
    ∃ FZ DZ : ℕ, {u : Fin (a+b+1) → ℝ | ∀ j : Fin b, u (Fin.castSucc (Fin.natAdd a j)) = 0}
      ∈ S.Ω FZ DZ (a+b+1) := by
  have h1 : ∀ j : Fin b, {u : Fin (a+b+1) → ℝ | u (Fin.castSucc (Fin.natAdd a j)) = 0} ∈
      S.Ω (a+b+1) ((Polynomial.C 1).eval D) (a+b+1) :=
    fun j => coordZero_mem S D (Fin.castSucc (Fin.natAdd a j))
  have h := S.inter (F := a+b+1) (n := a+b+1) (k := b)
    (D := fun _ : Fin b => (Polynomial.C 1).eval D)
    (A := fun j : Fin b => {u : Fin (a+b+1) → ℝ | u (Fin.castSucc (Fin.natAdd a j)) = 0}) h1
  have hset : (⋂ j : Fin b, {u : Fin (a+b+1) → ℝ | u (Fin.castSucc (Fin.natAdd a j)) = 0})
      = {u : Fin (a+b+1) → ℝ | ∀ j : Fin b, u (Fin.castSucc (Fin.natAdd a j)) = 0} := by
    ext u; simp
  exact ⟨a+b+1+1, ∑ _ : Fin b, ((Polynomial.C 1).eval D), by rwa [hset] at h⟩

/-- **The graph of the flat sheet is `Ω`-definable.** -/
private theorem flatGraph_mem (S : WilkiesDesign.SOMin) {a b F D : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1)) :
    ∃ F' D' : ℕ, WilkiesDesign.graphOf (fun w : Fin a → ℝ => G w 0) ∈ S.Ω F' D' (a + 1) := by
  set Z : Set (Fin (a+b+1) → ℝ) :=
    {u | ∀ j : Fin b, u (Fin.castSucc (Fin.natAdd a j)) = 0} with hZdef
  obtain ⟨FZ, DZ, hZmem⟩ := zeroFibre_mem S a b D
  have hZ'mem : Z ∈ S.Ω FZ DZ (a+b+1) := hZmem
  -- the joint set `famGraph G ∩ Z`
  have hX : ∃ F0 D0 : ℕ, WilkiesDesign.CG.famGraph G ∩ Z ∈ S.Ω F0 D0 (a+b+1) := by
    have h1 : WilkiesDesign.CG.famGraph G ∈ S.Ω (max F FZ) D (a+b+1) :=
      Work.WilG1.Omega.mono hG (le_max_left _ _) le_rfl
    have h2 : Z ∈ S.Ω (max F FZ) DZ (a+b+1) :=
      Work.WilG1.Omega.mono hZ'mem (le_max_right _ _) le_rfl
    refine ⟨max F FZ + 1, D + DZ, ?_⟩
    have h := S.inter (F := max F FZ) (n := a+b+1) (k := 2)
      (D := fun i : Fin 2 => if i = 0 then D else DZ)
      (A := fun i : Fin 2 => if i = 0 then WilkiesDesign.CG.famGraph G else Z)
      (by intro i; fin_cases i <;> simpa using ‹_›)
    rw [show (∑ i : Fin 2, (if i = 0 then D else DZ)) = D + DZ from by
      simp [Fin.sum_univ_two]] at h
    rwa [Work.WilG1.Omega.iInter_fin_two] at h
  obtain ⟨F0, D0, hXmem⟩ := hX
  obtain ⟨K, p, hp⟩ := Work.WilG4b.projCoords_mem (S := S) (m := a+b+1) (N := a+1) (flatE a b)
  have himg := hp F0 D0 _ hXmem
  refine ⟨F0 + K, Polynomial.eval D0 p, ?_⟩
  have hset : {y : Fin (a+1) → ℝ | ∃ x ∈ (WilkiesDesign.CG.famGraph G ∩ Z), y = x ∘ flatE a b}
      = WilkiesDesign.graphOf (fun w : Fin a → ℝ => G w 0) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxG, hxZ⟩, rfl⟩
      rw [WilkiesDesign.CG.famGraph] at hxG
      simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq] at hxG ⊢
      have hfib : (fun j : Fin b => Fin.init x (Fin.natAdd a j)) = 0 := by
        funext j
        simp only [Pi.zero_apply]
        show x (Fin.castSucc (Fin.natAdd a j)) = 0
        rw [hZdef] at hxZ
        exact hxZ j
      have hpar : Fin.init (x ∘ flatE a b) = (fun i : Fin a => Fin.init x (Fin.castAdd b i)) := by
        funext i
        show x (flatE a b (Fin.castSucc i)) = x (Fin.castSucc (Fin.castAdd b i))
        rw [show (Fin.castSucc i : Fin (a+1)) = Fin.castAdd 1 i from Fin.ext rfl,
          flatE_castAdd a b i]
        exact congrArg x (Fin.ext rfl)
      have hlast : (x ∘ flatE a b) (Fin.last a) = x (Fin.last (a+b)) := by
        simp only [Function.comp_apply, flatE_last]
      rw [hlast, hxG, ← hpar, ← hfib]
    · intro hy
      simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq] at hy
      set x : Fin (a+b+1) → ℝ :=
        Fin.snoc (Fin.append (Fin.init y) (0 : Fin b → ℝ)) (y (Fin.last a)) with hxdef
      have hxinit : Fin.init x = Fin.append (Fin.init y) (0 : Fin b → ℝ) := by
        funext k
        show x (Fin.castSucc k) = Fin.append (Fin.init y) (0 : Fin b → ℝ) k
        rw [hxdef]
        simp
      have hxlast : x (Fin.last (a+b)) = y (Fin.last a) := by
        rw [hxdef]; simp
      refine ⟨x, ⟨?_, ?_⟩, ?_⟩
      · rw [WilkiesDesign.CG.famGraph]
        simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq]
        have hpar : (fun i : Fin a => Fin.init x (Fin.castAdd b i)) = Fin.init y := by
          funext i
          rw [hxinit]
          simp
        have hfib : (fun j : Fin b => Fin.init x (Fin.natAdd a j)) = 0 := by
          funext j
          rw [hxinit]
          simp
        rw [hxlast, hpar, hfib, hy]
      · rw [hZdef]
        intro j
        show Fin.init x (Fin.natAdd a j) = 0
        rw [hxinit]
        simp
      · funext i
        refine Fin.addCases (m := a) (n := 1) (fun i' : Fin a => ?_) (fun i'' : Fin 1 => ?_) i
        · show y (Fin.castAdd 1 i') = x (flatE a b (Fin.castAdd 1 i'))
          have h1 : (Fin.castAdd 1 i' : Fin (a+1)) = Fin.castSucc i' := Fin.ext rfl
          rw [flatE_castAdd a b i', h1]
          have h2 : (Fin.castSucc (Fin.castAdd b i') : Fin (a+b+1)) = Fin.castAdd (b+1) i' :=
            Fin.ext rfl
          rw [← h2]
          show Fin.init y i' = Fin.init x (Fin.castAdd b i')
          rw [hxinit]
          simp
        · show y (Fin.natAdd a i'') = x (flatE a b (Fin.natAdd a i''))
          have h0 : (Fin.natAdd a i'' : Fin (a+1)) = Fin.last a := by
            ext; simp [Fin.natAdd, Fin.last]
          rw [h0, flatE_last, hxlast]
  rw [← hset]
  exact himg

/-- **N4 (the flat-sheet normal form).**  `G` definable; its `z`-slices are `C^1` on a ball;
it is jointly `C^1` at every off-sheet point over the open nonempty `Q`.  Then `G` is jointly
`C^1` at some sheet point `(w,0)`, `w ∈ Q`.

Proof: `b(w) := fderiv ℝ (G w) 0` and `a(w) := G w 0`; the graph of `a` is a projection of
`famGraph G`, so `WilkiesDesign.CG.G1_generic_smooth_proved` (or `c1Locus_dense`) gives that the
`C¹`-locus of `a` is open dense.  Apply `SliceDerivJointContV2` (N4b) and `ParamDerivJoint` (N4d)
to `G` on the open `Q` (feeding N4d the `Q1` of N4b, which still contains `Q` in its closure) and
let `Q6 := Q ∩ Q1 ∩ Q5 ∩ {w : ContDiffAt ℝ 1 (fun w => G w 0) w}`, which is open and nonempty
(a finite intersection of dense open subsets of the Baire space `Q`).  `C1Assembly` (N4e) with
`ha`, `hz` (the first conjunct of N4b) and `hw` (N4d) then gives
`ContDiffAt ℝ 1 (famFun G) (Fin.append w 0)` for `w ∈ Q6 ⊆ Q`. -/
theorem FlatSheetClean (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {a b F D : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (Q : Set (Fin a → ℝ)) (hQ : IsOpen Q) (hQne : Q.Nonempty) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z)) :
    ∃ w ∈ Q, ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w 0) := by
  -- The sheet function `a w := G w 0` is definable: its graph is a projection of `famGraph G`
  -- (intersected with the hyperplane "fibre coordinate `= 0`").
  obtain ⟨F', D', hgraph⟩ := flatGraph_mem S (G := G) hG
  -- Generic smoothness: the non-`C¹` locus of `a` has empty interior, so the `C¹`-locus `A` of
  -- `a` is dense.
  have hthin : interior {w : Fin a → ℝ | ¬ ContDiffAt ℝ 1 (fun w : Fin a → ℝ => G w 0) w} = ∅ :=
    Work.WilkG4c.interior_compl_contDiffAt S hcd (fun w : Fin a → ℝ => G w 0) hgraph (k := 1)
  set A : Set (Fin a → ℝ) := {w | ContDiffAt ℝ 1 (fun w : Fin a → ℝ => G w 0) w} with hAdef
  have hthinA : interior Aᶜ = ∅ := by
    have hset : Aᶜ = {w : Fin a → ℝ | ¬ ContDiffAt ℝ 1 (fun w : Fin a → ℝ => G w 0) w} := by
      rw [hAdef]; rfl
    rw [hset]; exact hthin
  have hAopen : IsOpen A := by
    rw [hAdef]
    exact Work.WilkG4c.isOpen_contDiffAt_set (k := 1) (fun w : Fin a → ℝ => G w 0)
  have hclos : closure A = Set.univ := by
    rw [← compl_compl (closure A), ← interior_compl, hthinA]
    simp
  have hdense : Dense A := by
    rw [Dense]; intro x; rw [hclos]; exact Set.mem_univ x
  -- N4b: an open `Q1 ⊆ Q` with `Q ⊆ closure Q1` on which the slice derivative at the sheet is
  -- uniformly continuous, together with the continuity of `w ↦ fderiv ℝ (G w) 0`.
  obtain ⟨Q1, hQ1open, hQ1sub, hQ1clos, hz1, _hb1⟩ :=
    SliceDerivJointNorm S hcd G hG Q hQ r0 hr0 hsl hoff
  -- N4d: an open `Q5 ⊆ Q1` with `Q1 ⊆ closure Q5` carrying the joint convergence of the
  -- parameter partials along the punctured sheet.
  obtain ⟨Q5, hQ5open, hQ5sub, hQ5clos, hw5⟩ :=
    ParamDerivJoint S hcd G hG Q1 hQ1open r0 hr0
      (fun w hw => hsl w (hQ1sub hw))
      (fun w hw z hz hlt => hoff w (hQ1sub hw) z hz hlt) hz1
  -- `Q5` is nonempty because `Q` is nonempty and `Q ⊆ closure Q1 ⊆ closure Q5`.
  have hQ5ne : Q5.Nonempty := by
    obtain ⟨w0, hw0⟩ := hQne
    have hw0cl : w0 ∈ closure Q5 := by
      simpa only [closure_closure] using closure_mono hQ5clos (hQ1clos hw0)
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hw0cl
    exact hw0cl
  -- `Q6 := Q5 ∩ A` is open and nonempty (a nonempty open set meets the dense `A`).
  have hQ6ne : (Q5 ∩ A).Nonempty := hdense.inter_open_nonempty Q5 hQ5open hQ5ne
  have hQ6open : IsOpen (Q5 ∩ A) := hQ5open.inter hAopen
  -- All the hypotheses of the `C¹` assembly `N4e` restrict to `Q6 ⊆ Q1 ⊆ Q`.
  have hsl6 : ∀ w ∈ Q5 ∩ A, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0) :=
    fun w hw => hsl w (hQ1sub (hQ5sub hw.1))
  have hoff6 : ∀ w ∈ Q5 ∩ A, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z) :=
    fun w hw z hz hlt => hoff w (hQ1sub (hQ5sub hw.1)) z hz hlt
  have ha6 : ContDiffOn ℝ 1 (fun w : Fin a → ℝ => G w 0) (Q5 ∩ A) := by
    intro w hw
    have hwA : ContDiffAt ℝ 1 (fun w : Fin a → ℝ => G w 0) w := by
      have hmem := hw.2
      rwa [hAdef] at hmem
    exact hwA.contDiffWithinAt
  have hz6 : ∀ w₀ ∈ Q5 ∩ A, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε :=
    fun w₀ hw => hz1 w₀ (hQ5sub hw.1)
  have hw6 : ∀ w₀ ∈ Q5 ∩ A, ∀ i : Fin a, Filter.Tendsto
      (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
        fderiv ℝ (Work.WilG4c.famFun G) (Fin.append p.1 p.2) (Fin.append (Pi.single i 1) 0)
          - fderiv ℝ (fun w' => G w' 0) p.1 (Pi.single i 1))
      (nhdsWithin (w₀, 0) {p : (Fin a → ℝ) × (Fin b → ℝ) | p.2 ≠ 0}) (nhds 0) :=
    fun w₀ hw => hw5 w₀ hw.1
  have hres := C1Assembly G (Q5 ∩ A) hQ6open r0 hr0 hsl6 hoff6 ha6 hz6 hw6
  obtain ⟨w, hwQ5, hwA⟩ := hQ6ne
  exact ⟨w, hQ1sub (hQ5sub hwQ5), hres w ⟨hwQ5, hwA⟩⟩

end Work.WilCruxN
