/-
  WilG4c — `DescentP`: the F-lemma `FLemP` descends from parameter dimension `p` to any
  parameter dimension `q ≤ p`.

  Given `FLemP S p N P`, a `q`-parameter family `F` is lifted to the `p`-parameter family
  `liftFam hpq F` (exactly the family appearing in the bridge hypothesis `hPQ`); the charts
  produced at dimension `p` are restricted back to `q` parameters by filling the extra
  parameters in with `parOf` (`resChart`).  Both operations are coordinate reindexings of the
  ambient space `ℝ^{·+N+1}` (a slice at the parameter `0` when `q = 0`), so the `Ω`-membership
  of the family graph and of the chart graphs is preserved at the cost of constants depending
  only on `p, q, N`; the two polynomial witnesses of the conclusion are shifted accordingly
  (`D ↦ D + B`).

  The file is deliberately self-contained (only pre-existing modules are imported): it carries
  the `Ω`-bookkeeping (`famGraph_liftFam_mem`, `famGraph_resChart_mem`, and the slice
  computation for `q = 0`) together with the descent argument itself.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG4a.CD.eval_bind_shift

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The parameter extension, the lift of a family and the restriction of a chart -/

def hpar {q p : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) (a : Fin p) : Fin q :=
  if ha : a.val < q then ⟨a.val, ha⟩ else ⟨0, Nat.pos_of_ne_zero hq⟩

theorem hpar_castLE {q p : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) (a : Fin q) :
    hpar hpq hq (Fin.castLE hpq a) = a := by
  simp [hpar]

/-- The extension of a `q`-parameter vector to `p` parameters by repeating the first
parameter in the extra slots. -/
def extPar {q p : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) (l : Fin q → ℝ) : Fin p → ℝ :=
  fun a => l (hpar hpq hq a)

theorem extPar_castLE {q p : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) (l : Fin q → ℝ) (a : Fin q) :
    extPar hpq hq l (Fin.castLE hpq a) = l a := by
  simp [extPar, hpar]

/-- The parameter vector fed to a `p`-parameter chart by a `q`-parameter one: `extPar` when
`q ≠ 0`, the constant `0` when `q = 0` (no retraction exists in that case). -/
def parOf {q p : ℕ} (hpq : q ≤ p) (l : Fin q → ℝ) : Fin p → ℝ :=
  if h : q = 0 then (fun _ => 0) else extPar hpq h l

theorem parOf_eq_extPar {q p : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) (l : Fin q → ℝ) :
    parOf hpq l = extPar hpq hq l := by
  rw [parOf, dif_neg hq]

theorem parOf_zero {p : ℕ} (hpq : 0 ≤ p) (l : Fin 0 → ℝ) :
    parOf hpq l = (fun _ : Fin p => (0 : ℝ)) := by
  funext a
  rw [parOf, dif_pos rfl]

/-- Composition of the parameter extension with `Fin.castLE hpq` is the identity. -/
theorem parOf_castLE {q p : ℕ} (hpq : q ≤ p) (l : Fin q → ℝ) :
    (fun j : Fin q => parOf hpq l (Fin.castLE hpq j)) = l := by
  by_cases hq : q = 0
  · subst hq
    funext j
    exact j.elim0
  · rw [parOf_eq_extPar hpq hq l]
    funext j
    exact extPar_castLE hpq hq l j

/-! ## 2. Lifting a family and restricting a chart -/

/-- The `p`-parameter lift of a `q`-parameter family: the extra parameters are ignored. -/
def liftFam {k q p N : ℕ} (hpq : q ≤ p) (F : Family k q N) : Family k p N :=
  fun i l z => F i (fun j => l (Fin.castLE hpq j)) z

/-- The `q`-parameter restriction of a `p`-parameter chart: the extra parameters of the chart
are filled in by `parOf`. -/
def resChart {q p N : ℕ} (hpq : q ≤ p) (φ : ChartTuple p N) : ChartTuple q N :=
  fun j l t => φ j (parOf hpq l) t

/-- The lifted family at the parameter fed to a restricted chart agrees with the original family
on the corresponding `q`-parameters. -/
theorem liftFam_apply_parOf {k q p N : ℕ} (hpq : q ≤ p) (F : Family k q N) (i : Fin k)
    (l : Fin q → ℝ) (z : Fin N → ℝ) :
    liftFam hpq F i (parOf hpq l) z = F i l z := by
  simp only [liftFam, parOf_castLE hpq l]

/-! ## 3. The index maps and their computation rules -/

theorem last_eq_natAdd_last (q N : ℕ) :
    (Fin.last (q + N) : Fin (q + (N + 1))) = Fin.natAdd q (Fin.last N) :=
  Fin.ext rfl

theorem natAdd_castSucc (q N : ℕ) (j : Fin N) :
    ((Fin.natAdd q j).castSucc : Fin (q + (N + 1))) = Fin.natAdd q j.castSucc :=
  Fin.ext rfl

/-- The index inclusion `Fin (q+N+1) → Fin (p+N+1)`: the `q` parameters sit in the first
`q` parameter slots, the remaining `N+1` coordinates are unchanged. -/
def idxIn {q p : ℕ} (hpq : q ≤ p) (N : ℕ) : Fin (q + N + 1) → Fin (p + N + 1) :=
  fun i => Fin.addCases (motive := fun _ : Fin (q + (N + 1)) => Fin (p + N + 1))
    (fun a : Fin q => Fin.castAdd (N + 1) (Fin.castLE hpq a))
    (fun b : Fin (N + 1) => Fin.natAdd p b) i

theorem idxIn_castAdd {q p N : ℕ} (hpq : q ≤ p) (a : Fin q) :
    idxIn hpq N (Fin.castAdd (N + 1) a) = Fin.castAdd (N + 1) (Fin.castLE hpq a) := by
  simp only [idxIn, Fin.addCases_left]

theorem idxIn_natAdd {q p N : ℕ} (hpq : q ≤ p) (b : Fin (N + 1)) :
    idxIn hpq N (Fin.natAdd q b) = Fin.natAdd p b := by
  simp only [idxIn, Fin.addCases_right]

theorem idxIn_last {q p N : ℕ} (hpq : q ≤ p) :
    idxIn hpq N (Fin.last (q + N)) = Fin.last (p + N) := by
  rw [last_eq_natAdd_last]
  simp only [idxIn, Fin.addCases_right]
  exact Fin.ext rfl

/-- The index map `Fin (p+N+1) → Fin (q+N+1)` reading a point of `ℝ^{p+N+1}` as
`(l ∘ hpar, t, y)`. -/
def idxRetr {q p : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) (N : ℕ) :
    Fin (p + N + 1) → Fin (q + N + 1) :=
  fun i => Fin.addCases (motive := fun _ : Fin (p + (N + 1)) => Fin (q + N + 1))
    (fun a : Fin p => Fin.castAdd (N + 1) (hpar hpq hq a))
    (fun b : Fin (N + 1) => Fin.natAdd q b) i

theorem idxRetr_castAdd {q p N : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) (a : Fin p) :
    idxRetr hpq hq N (Fin.castAdd (N + 1) a) = Fin.castAdd (N + 1) (hpar hpq hq a) := by
  simp only [idxRetr, Fin.addCases_left]

theorem idxRetr_natAdd {q p N : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) (b : Fin (N + 1)) :
    idxRetr hpq hq N (Fin.natAdd p b) = Fin.natAdd q b := by
  simp only [idxRetr, Fin.addCases_right]

theorem idxRetr_last {q p N : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) :
    idxRetr hpq hq N (Fin.last (p + N)) = Fin.last (q + N) := by
  rw [last_eq_natAdd_last]
  simp only [idxRetr, Fin.addCases_right]
  exact Fin.ext rfl

/-! ## 4. The two graph computations -/

/-- The family graph of the lift is the coordinate preimage of the family graph along `idxIn`. -/
theorem famGraph_liftFam {q p N k : ℕ} (hpq : q ≤ p) (F : Family k q N) (i : Fin k) :
    famGraph (liftFam hpq F i) =
      Work.WilG5.coordPre (idxIn hpq N) (famGraph (F i)) := by
  ext x
  simp only [famGraph, graphOf, Work.WilG5.coordPre, Set.mem_ofPred_eq, Fin.init,
    Function.comp_apply, liftFam, idxIn_castAdd, idxIn_natAdd, idxIn_last,
    Fin.castSucc_castAdd, natAdd_castSucc]

/-- The graph of the restricted chart is the coordinate preimage of the chart graph along
`idxRetr` (the case `q ≠ 0`). -/
theorem famGraph_resChart_ne {q p N : ℕ} (hpq : q ≤ p) (hq : q ≠ 0) (φ : ChartTuple p N)
    (j : Fin N) :
    famGraph (resChart hpq φ j) =
      Work.WilG5.coordPre (idxRetr hpq hq N) (famGraph (φ j)) := by
  ext x
  simp only [famGraph, graphOf, Work.WilG5.coordPre, Set.mem_ofPred_eq, Fin.init,
    Function.comp_apply, resChart, parOf_eq_extPar hpq hq, extPar,
    idxRetr_castAdd, idxRetr_natAdd, idxRetr_last, hpar_castLE,
    Fin.castSucc_castAdd, natAdd_castSucc]
  try rfl

/-! ## 2. `Ω`-bookkeeping for the lift and for the restricted charts -/

theorem mem_graphOf {n : ℕ} {g : (Fin n → ℝ) → ℝ} {z : Fin (n + 1) → ℝ} :
    z ∈ graphOf g ↔ z (Fin.last n) = g (Fin.init z) :=
  Iff.rfl

theorem mem_famGraph {p n : ℕ} {G : (Fin p → ℝ) → (Fin n → ℝ) → ℝ} {z : Fin (p + n + 1) → ℝ} :
    z ∈ famGraph G ↔
      z (Fin.last (p + n)) = G (fun i : Fin p => z ((Fin.castAdd n i).castSucc))
        (fun j : Fin n => z ((Fin.natAdd p j).castSucc)) :=
  Iff.rfl

theorem mem_liftFirst {m k : ℕ} {A : Set (Fin m → ℝ)} {z : Fin (m + k) → ℝ} :
    z ∈ Work.WilG5.liftFirst k A ↔ (fun i : Fin m => z (Fin.castAdd k i)) ∈ A :=
  Iff.rfl

/-! ## 1. The family lift -/

/-- The graphs of a `q`-parameter family and of its `p`-parameter lift differ by a coordinate
reindexing, so `Ω`-membership is preserved at the cost of constants depending only on `p, q, N`. -/
theorem famGraph_liftFam_mem (S : SOMin) {q p N : ℕ} (hpq : q ≤ p) :
    ∃ A B : ℕ, ∀ {k : ℕ} (F : Family k q N) (i : Fin k) {F0 D : ℕ},
      famGraph (F i) ∈ S.Ω F0 D (q + N + 1) →
      famGraph (liftFam hpq F i) ∈ S.Ω (F0 + A) (D + B) (p + N + 1) := by
  refine ⟨64 * ((p + N + 1) + (q + N + 1)) + 64, 32 * ((p + N + 1) + (q + N + 1)) + 32, ?_⟩
  intro k F i F0 D h
  rw [famGraph_liftFam hpq F i]
  have h1 := Work.WilG5.coordPre_mem (S := S) (m := q + N + 1) (N := p + N + 1)
    (ι := idxIn hpq N) (F := F0) (D := D) (A := famGraph (F i)) h
  simpa only [Nat.add_assoc] using h1

/-! ## 2. The polynomial shifts -/

/-- Absorbing a shift of the first variable of a `ℕ`-coefficient polynomial into a
substitution: `b'(D,r) = b(D+K, r)`. -/
theorem natPoly_shift (b : MvPolynomial (Fin 2) ℕ) (K : ℕ) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![D + K, r] b = MvPolynomial.eval ![D, r] b' := by
  refine ⟨MvPolynomial.aeval
    (![MvPolynomial.X 0 + MvPolynomial.C K, MvPolynomial.X 1] :
      Fin 2 → MvPolynomial (Fin 2) ℕ) b, ?_⟩
  intro D r
  rw [Work.WilG4a.CD.eval_aeval_eq (![D, r] : Fin 2 → ℕ)
    (![MvPolynomial.X 0 + MvPolynomial.C K, MvPolynomial.X 1] :
      Fin 2 → MvPolynomial (Fin 2) ℕ) b]
  have hfun : (fun i : Fin 2 => MvPolynomial.eval (![D, r] : Fin 2 → ℕ)
      ((![MvPolynomial.X 0 + MvPolynomial.C K, MvPolynomial.X 1] :
        Fin 2 → MvPolynomial (Fin 2) ℕ) i)) = (![D + K, r] : Fin 2 → ℕ) := by
    funext i
    fin_cases i <;> simp
  rw [hfun]

/-- Absorbing a shift of the first variable of a real polynomial into a substitution:
`c'(D,r,k,u) = c(D+K, r, k, u)`. -/
theorem poly_shift (c : MvPolynomial (Fin 4) ℝ) (K : ℕ) :
    ∃ c' : MvPolynomial (Fin 4) ℝ, ∀ (D r k : ℕ) (L : ℝ),
      MvPolynomial.eval ![(D : ℝ) + (K : ℝ), (r : ℝ), (k : ℝ), L] c =
        MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] c' := by
  refine ⟨MvPolynomial.aeval
    (![MvPolynomial.X 0 + MvPolynomial.C (K : ℝ), MvPolynomial.X 1, MvPolynomial.X 2,
      MvPolynomial.X 3] : Fin 4 → MvPolynomial (Fin 4) ℝ) c, ?_⟩
  intro D r k L
  rw [Work.WilG4a.CD.eval_aeval_eq (![(D : ℝ), (r : ℝ), (k : ℝ), L] : Fin 4 → ℝ)
    (![MvPolynomial.X 0 + MvPolynomial.C (K : ℝ), MvPolynomial.X 1, MvPolynomial.X 2,
      MvPolynomial.X 3] : Fin 4 → MvPolynomial (Fin 4) ℝ) c]
  have hfun : (fun i : Fin 4 => MvPolynomial.eval (![(D : ℝ), (r : ℝ), (k : ℝ), L] : Fin 4 → ℝ)
      ((![MvPolynomial.X 0 + MvPolynomial.C (K : ℝ), MvPolynomial.X 1, MvPolynomial.X 2,
        MvPolynomial.X 3] : Fin 4 → MvPolynomial (Fin 4) ℝ) i))
      = (![(D : ℝ) + (K : ℝ), (r : ℝ), (k : ℝ), L] : Fin 4 → ℝ) := by
    funext i
    fin_cases i <;> simp
  rw [hfun]

/-! ## 3. The chart restriction -/

/-! ### 3a. Index bookkeeping for the `q = 0` slice -/

theorem fin_cast_last {N : ℕ} (h : N + 1 = 0 + N + 1) :
    Fin.cast h (Fin.last N) = (Fin.last (0 + N) : Fin (0 + N + 1)) :=
  Fin.ext (by simp)

theorem fin_cast_castSucc {N : ℕ} (h : N + 1 = 0 + N + 1) (b : Fin N) :
    Fin.cast h b.castSucc = ((Fin.natAdd 0 b).castSucc : Fin (0 + N + 1)) :=
  Fin.ext (by simp)

/-! ### 3b. The slice at the parameter `0` -/

/-- The graph of `t ↦ φ j 0 t` (the `p`-parameter chart at the parameter `0`, in the
`N+1`-dimensional ambient) is the image of the graph of `φ j` restricted to the hyperplane
`l = 0`, under the projection to the last `N+1` coordinates. -/
theorem slice_graphOf_eq {p N : ℕ} (φ : ChartTuple p N) (j : Fin N) :
    graphOf (fun t : Fin N → ℝ => φ j (0 : Fin p → ℝ) t) =
      Work.WilG5.coordImage (Fin.natAdd p : Fin (N + 1) → Fin (p + N + 1))
        (famGraph (φ j) ∩ Work.WilG5.liftFirst (N + 1) ({0} : Set (Fin p → ℝ))) := by
  ext u
  rw [mem_graphOf]
  constructor
  · intro hu
    refine ⟨Fin.append (0 : Fin p → ℝ) u, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_famGraph]
      have hL : (Fin.append (0 : Fin p → ℝ) u) (Fin.last (p + N)) = u (Fin.last N) := by
        rw [show (Fin.last (p + N) : Fin (p + (N + 1))) = Fin.natAdd p (Fin.last N)
          from Fin.ext rfl, Fin.append_right]
      have h1 : (fun a : Fin p => (Fin.append (0 : Fin p → ℝ) u) ((Fin.castAdd N a).castSucc))
          = (0 : Fin p → ℝ) := by
        funext a
        rw [show (Fin.castAdd N a).castSucc = (Fin.castAdd (N + 1) a : Fin (p + (N + 1)))
          from Fin.ext rfl, Fin.append_left]
      have h2 : (fun b : Fin N => (Fin.append (0 : Fin p → ℝ) u) ((Fin.natAdd p b).castSucc))
          = Fin.init u := by
        funext b
        rw [show (Fin.natAdd p b).castSucc = (Fin.natAdd p b.castSucc : Fin (p + (N + 1)))
          from Fin.ext rfl, Fin.append_right]
        rfl
      calc (Fin.append (0 : Fin p → ℝ) u) (Fin.last (p + N))
          = u (Fin.last N) := hL
        _ = φ j (0 : Fin p → ℝ) (Fin.init u) := hu
        _ = φ j (fun a : Fin p => (Fin.append (0 : Fin p → ℝ) u) ((Fin.castAdd N a).castSucc))
              (fun b : Fin N => (Fin.append (0 : Fin p → ℝ) u) ((Fin.natAdd p b).castSucc)) := by
            rw [h1, h2]
    · rw [mem_liftFirst, Set.mem_singleton_iff]
      funext a
      simp [Fin.append_left]
    · funext b
      exact Fin.append_right (0 : Fin p → ℝ) u b
  · rintro ⟨x, ⟨hxA, hx0⟩, hxu⟩
    rw [mem_famGraph] at hxA
    rw [mem_liftFirst, Set.mem_singleton_iff] at hx0
    have h1 : (fun a : Fin p => x ((Fin.castAdd N a).castSucc)) = (0 : Fin p → ℝ) := by
      funext a
      have h := congrFun hx0 a
      rw [show (Fin.castAdd N a).castSucc = (Fin.castAdd (N + 1) a : Fin (p + (N + 1)))
        from Fin.ext rfl]
      exact h
    have h2 : (fun b : Fin N => x ((Fin.natAdd p b).castSucc)) = Fin.init u := by
      funext b
      have h := congrFun hxu b.castSucc
      rw [Function.comp_apply] at h
      rw [show (Fin.natAdd p b).castSucc = (Fin.natAdd p b.castSucc : Fin (p + (N + 1)))
        from Fin.ext rfl, h]
      rfl
    rw [h1, h2] at hxA
    have hmid : x (Fin.natAdd p (Fin.last N)) = u (Fin.last N) := by
      have h := congrFun hxu (Fin.last N)
      rwa [Function.comp_apply] at h
    rw [show (Fin.last (p + N) : Fin (p + (N + 1))) = Fin.natAdd p (Fin.last N)
      from Fin.ext rfl] at hxA
    rw [← hmid]
    exact hxA

/-! ### 3c. The graph of the restricted chart as a slice -/

/-- For `q = 0` the graph of the restricted chart is the transport of the graph of the chart
`t ↦ φ j 0 t` from the `N+1`- to the `0+N+1`-dimensional ambient. -/
theorem famGraph_resChart_zero_eq {p N : ℕ} (hpq : 0 ≤ p) (φ : ChartTuple p N) (j : Fin N)
    (h : N + 1 = 0 + N + 1) :
    famGraph (resChart hpq φ j) =
      (h ▸ graphOf (fun t : Fin N → ℝ => φ j (0 : Fin p → ℝ) t)) := by
  ext w
  rw [Work.WilG5.mem_ndrec]
  set u : Fin (N + 1) → ℝ := fun i => w (Fin.cast h i) with hu
  rw [mem_graphOf, mem_famGraph]
  have hcast : u (Fin.last N) = w (Fin.last (0 + N)) := by
    rw [hu]
    exact congrArg w (fin_cast_last h)
  have hsub : (fun j : Fin N => w ((Fin.natAdd 0 j).castSucc)) = Fin.init u := by
    funext b
    rw [hu]
    exact congrArg w (fin_cast_castSucc h b).symm
  have hres : resChart hpq φ j (fun i : Fin 0 => w ((Fin.castAdd N i).castSucc)) (Fin.init u)
      = φ j (0 : Fin p → ℝ) (Fin.init u) := by
    rw [show resChart hpq φ j (fun i : Fin 0 => w ((Fin.castAdd N i).castSucc)) (Fin.init u)
        = φ j (parOf hpq (fun i : Fin 0 => w ((Fin.castAdd N i).castSucc))) (Fin.init u)
        from rfl]
    rw [parOf_zero]
    rfl
  have hP1 : (u (Fin.last N) = φ j (0 : Fin p → ℝ) (Fin.init u)) ↔
      (w (Fin.last (0 + N)) = resChart hpq φ j (fun i : Fin 0 => w ((Fin.castAdd N i).castSucc))
        (fun j : Fin N => w ((Fin.natAdd 0 j).castSucc))) := by
    rw [hcast, hsub, hres]
  have hP2 : (u ∈ graphOf (fun t : Fin N → ℝ => φ j (0 : Fin p → ℝ) t)) ↔
      (u (Fin.last N) = φ j (0 : Fin p → ℝ) (Fin.init u)) := mem_graphOf
  have hP3 : (w ∈ famGraph (resChart hpq φ j)) ↔
      (w (Fin.last (0 + N)) = resChart hpq φ j (fun i : Fin 0 => w ((Fin.castAdd N i).castSucc))
        (fun j : Fin N => w ((Fin.natAdd 0 j).castSucc))) := mem_famGraph
  exact hP3.trans (hP1.symm.trans hP2.symm)

/-! ### 3d. The `Ω`-membership of the restricted chart graph -/

/-- The graph of a restricted chart is `Ω`-bounded in dimension `q + N + 1`, at the cost of
constants depending only on `q, p, N`. -/
theorem famGraph_resChart_mem (S : SOMin) {q p N : ℕ} (hpq : q ≤ p) :
    ∃ A B : ℕ, ∀ (φ : ChartTuple p N) (j : Fin N) {a Dg : ℕ},
      famGraph (φ j) ∈ S.Ω a Dg (p + N + 1) →
      famGraph (resChart hpq φ j) ∈ S.Ω (a + A) (Dg + B) (q + N + 1) := by
  by_cases hq : q = 0
  · subst hq
    set h : N + 1 = 0 + N + 1 := by omega with hh
    set A : ℕ := 4 * p + 20 + (N + 1) + 1 + 64 * ((p + (N + 1)) + (N + 1)) + 64 with hA
    set B : ℕ := 4 * p + 4 + 32 * ((p + (N + 1)) + (N + 1)) + 32 with hB
    refine ⟨A, B, ?_⟩
    intro φ j a Dg hpd
    have heq : famGraph (resChart hpq φ j) =
        (h ▸ Work.WilG5.coordImage (Fin.natAdd p : Fin (N + 1) → Fin (p + (N + 1)))
          (famGraph (φ j) ∩ Work.WilG5.liftFirst (N + 1) ({0} : Set (Fin p → ℝ)))) := by
      rw [famGraph_resChart_zero_eq hpq φ j h, slice_graphOf_eq φ j]
    rw [heq]
    have h0 : ({0} : Set (Fin p → ℝ)) ∈ S.Ω (4 * p + 20) (4 * p + 4) p :=
      Work.WilG5.singleton_mem (S := S) 0
    have h1 : Work.WilG5.liftFirst (N + 1) ({0} : Set (Fin p → ℝ)) ∈
        S.Ω (4 * p + 20 + (N + 1)) (4 * p + 4) (p + (N + 1)) :=
      Work.WilG5.liftFirst_mem (S := S) (N + 1) (4 * p + 20) (4 * p + 4) h0
    have h' : famGraph (φ j) ∈ S.Ω (max a (4 * p + 20 + (N + 1))) Dg (p + (N + 1)) :=
      Work.WilG5.mem_mono hpd _ _ (le_max_left _ _) (le_refl _)
    have h1' : Work.WilG5.liftFirst (N + 1) ({0} : Set (Fin p → ℝ)) ∈
        S.Ω (max a (4 * p + 20 + (N + 1))) (4 * p + 4) (p + (N + 1)) :=
      Work.WilG5.mem_mono h1 _ _ (le_max_right _ _) (le_refl _)
    have hJ := S.inter (fun i : Fin 2 => if i = 0 then Dg else 4 * p + 4)
      (fun i : Fin 2 => if i = 0 then famGraph (φ j)
        else Work.WilG5.liftFirst (N + 1) ({0} : Set (Fin p → ℝ)))
      (by intro i; fin_cases i <;> simpa)
    rw [show (∑ i : Fin 2, (if i = 0 then Dg else 4 * p + 4)) = Dg + (4 * p + 4) from by
      simp [Fin.sum_univ_two]] at hJ
    have hJset : (⋂ i : Fin 2, (if i = 0 then famGraph (φ j)
        else Work.WilG5.liftFirst (N + 1) ({0} : Set (Fin p → ℝ)))) =
        famGraph (φ j) ∩ Work.WilG5.liftFirst (N + 1) ({0} : Set (Fin p → ℝ)) := by
      ext z; simp [Fin.forall_fin_two]
    rw [hJset] at hJ
    have hci := Work.WilG5.coordImage_mem (S := S) (m := N + 1) (N := p + (N + 1))
      (ι := (Fin.natAdd p : Fin (N + 1) → Fin (p + (N + 1)))) hJ
    exact Work.WilG5.omega_ndrec (S := S) h (Work.WilG5.mem_mono hci (a + A) (Dg + B)
      (by rw [hA]; omega) (by rw [hB]; omega))
  · refine ⟨64 * ((q + N + 1) + (p + N + 1)) + 64,
      32 * ((q + N + 1) + (p + N + 1)) + 32, ?_⟩
    intro φ j a Dg h
    rw [famGraph_resChart_ne hpq hq φ j]
    exact Work.WilG5.coordPre_mem (S := S) (m := p + N + 1) (N := q + N + 1)
      (ι := idxRetr hpq hq N) (F := a) (D := Dg) (A := famGraph (φ j)) h

/-! ## 3. The descent -/

theorem DescentP (S : WilkiesDesign.SOMin) (N p q : ℕ) (hpq : q ≤ p)
    (P : ℕ → ∀ k, Work.WilkG4c.Family k p N → Prop)
    (Q : ℕ → ∀ k, Work.WilkG4c.Family k q N → Prop)
    (hPQ : ∀ (r k : ℕ) (F' : Work.WilkG4c.Family k q N),
        Q r k F' → P r k (fun (i : Fin k) (l : Fin p → ℝ) (z : Fin N → ℝ) =>
          F' i (fun j => l (Fin.castLE hpq j)) z))
    (hh : Work.WilkG4c.FLemP S p N P) :
    Work.WilkG4c.FLemP S q N Q := by
  classical
  rw [FLemP_iff] at hh ⊢
  intro F0
  obtain ⟨A, B, hlif⟩ := famGraph_liftFam_mem S hpq
  obtain ⟨Ares, Bres, hres⟩ := famGraph_resChart_mem S hpq
  obtain ⟨a, b, c, hbody⟩ := hh (F0 + A)
  obtain ⟨b₁, hb₁⟩ := natPoly_shift b B
  obtain ⟨c', hc'⟩ := poly_shift c B
  refine ⟨a + Ares, b₁ + MvPolynomial.C Bres, c', ?_⟩
  intro D r k ε hε hε1 Λ F hQ hΩ hVal
  set Λ' : Set (Fin p → ℝ) := {l : Fin p → ℝ | (fun j : Fin q => l (Fin.castLE hpq j)) ∈ Λ}
    with hΛ'def
  have hmemΛ' : ∀ l : Fin q → ℝ, l ∈ Λ → parOf hpq l ∈ Λ' := by
    intro l hl
    rw [hΛ'def, Set.mem_ofPred_eq, parOf_castLE hpq l]
    exact hl
  have hΩ' : ∀ i : Fin k, famGraph (liftFam hpq F i) ∈ S.Ω (F0 + A) (D + B) (p + N + 1) :=
    fun i => hlif F i (hΩ i)
  have hVal' : ValuesIn01 Λ' (liftFam hpq F) := by
    intro i l' hl' x hx
    exact hVal i (fun j => l' (Fin.castLE hpq j)) hl' x hx
  obtain ⟨Φ, hcard, hok, hcov⟩ :=
    hbody (D + B) r k ε hε hε1 Λ' (liftFam hpq F) (hPQ r k F hQ) hΩ' hVal'
  refine ⟨Φ.image (fun φ => resChart hpq φ), ?_, ?_, ?_⟩
  · -- the cardinality of the new chart set is bounded by the old one
    have h1 : ((Φ.image (fun φ => resChart hpq φ)).card : ℝ) ≤ (Φ.card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    have hcast : ((D + B : ℕ) : ℝ) = (D : ℝ) + (B : ℝ) := by push_cast; ring
    rw [hcast] at hcard
    rw [hc'] at hcard
    exact le_trans h1 hcard
  · -- the per-chart conditions
    intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hψ
    have hφok := hok φ hφ
    refine ⟨?_, ?_⟩
    · intro j
      have hdeg : MvPolynomial.eval ![D + B, r] b + Bres ≤
          MvPolynomial.eval ![(D : ℕ), r] (b₁ + MvPolynomial.C Bres) := by
        rw [MvPolynomial.eval_add, MvPolynomial.eval_C, ← hb₁ D r]
      exact Work.WilG5.mem_mono (hres φ j (hφok.1 j)) (a + Ares) _ le_rfl hdeg
    · intro l hl
      have hl' : parOf hpq l ∈ Λ' := hmemΛ' l hl
      refine ⟨?_, ?_⟩
      · intro t ht
        simpa only [resChart] using (hφok.2 (parOf hpq l) hl').1 t ht
      · intro i
        have hc := hφok.2 (parOf hpq l) hl'
        have hfun : (fun t : Fin N → ℝ => F i l (fun j => resChart hpq φ j l t)) =
            (fun t : Fin N → ℝ =>
              liftFam hpq F i (parOf hpq l) (fun j => φ j (parOf hpq l) t)) := by
          funext t
          simp only [resChart, liftFam_apply_parOf]
        refine ⟨?_, ?_⟩
        · rw [hfun]
          exact (hc.2 i).1
        · intro m hm t ht
          rw [hfun]
          exact (hc.2 i).2 m hm t ht
  · -- the covering condition
    intro l hl x hx
    have hl' : parOf hpq l ∈ Λ' := hmemΛ' l hl
    obtain ⟨φ, hφ, t, ht, hlt⟩ := hcov (parOf hpq l) hl' x hx
    refine ⟨resChart hpq φ, Finset.mem_image_of_mem _ hφ, t, ht, fun i => ?_⟩
    simpa only [resChart, liftFam_apply_parOf] using hlt i

end Work.WilkG4c

/-! ## 4. The requested name

The area `Submission/Work/WilG4c` is in the middle of a namespace migration
(`Work.WilG4c` → `Work.WilkG4c`): the request for this lemma came in with the *old* spelling of
the namespace for the lemma's own name -- `Work.WilG4c.DescentP` (that is exactly the shape
recorded in the host state) -- while the vocabulary of its statement (`Family`, `FLemP`) is
declared in the *new* spelling `Work.WilkG4c`.  The proof therefore lives in `Work.WilkG4c`, and
below the very same statement is declared once more at the requested, old-spelling name.  Both
names denote the same lemma. -/

namespace Work.WilG4c

theorem DescentP (S : WilkiesDesign.SOMin) (N p q : ℕ) (hpq : q ≤ p)
    (P : ℕ → ∀ k, Work.WilkG4c.Family k p N → Prop)
    (Q : ℕ → ∀ k, Work.WilkG4c.Family k q N → Prop)
    (hPQ : ∀ (r k : ℕ) (F' : Work.WilkG4c.Family k q N),
        Q r k F' → P r k (fun (i : Fin k) (l : Fin p → ℝ) (z : Fin N → ℝ) =>
          F' i (fun j => l (Fin.castLE hpq j)) z))
    (hh : Work.WilkG4c.FLemP S p N P) :
    Work.WilkG4c.FLemP S q N Q :=
  Work.WilkG4c.DescentP S N p q hpq P Q hPQ hh

end Work.WilG4c
