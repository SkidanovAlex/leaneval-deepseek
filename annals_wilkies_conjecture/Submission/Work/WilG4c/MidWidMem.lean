/-
  WilG4c — the per-cell engine of BNZ §5.5: the midpoint and the shifted half-width of the
  fibre of a cell, evaluated at the base point `(l, χ l u)`.

  Writing `φ := flatMap χ` for the base-point map `(l,u) ↦ Fin.append l (χ l u)`, both
  `midFun lo hi χ` and `widFun lo hi χ` are obtained by composing an affine combination
  `w ↦ c₁ + c₂ * lo w + c₃ * hi w` of the two fibre ends with `φ`:

  * `midFun lo hi χ = (lo ∘ φ + hi ∘ φ)/2`, i.e. `(c₁, c₂, c₃) = (0, 1/2, 1/2)`;
  * `widFun lo hi χ = 1/4 + (hi ∘ φ - lo ∘ φ)/2`, i.e. `(c₁, c₂, c₃) = (1/4, -1/2, 1/2)`.

  Both steps are `Ω`-bounded with a format gain and a degree that are *affine* in the input
  degree `D`, with coefficients uniform in the data:

  * `affCombExp` (section 4) is the affine-combination lemma of area G4a
    (`Work.WilG4a.affine_comb_graph_mem`), re-proved with the explicit degree
    `2 * D + (4 * (m + 3) + 9)` in place of the two-variable `MvPolynomial` (which is
    `Work.WilG4a.bpoly`, with the same value, but hidden behind an existential);
  * `compExp` (section 3) is the substitution calculus of `Work.WilG4c.GraphOfComp`, re-proved
    with explicit format/degree increments.  `GraphOfComp` returns its increments
    *existentially after* the degree parameter, which yields increments that may depend on
    `D`; for the uniform statement needed here they have to be exhibited.

  The coordinate graphs of `flatMap χ` are the graphs of the coordinate projections (first `p`
  coordinates, `graphOf_coord_mw`, section 2) and the `famGraph`s of the coordinates of `χ`
  (last `n` coordinates).
-/
import Mathlib
import Submission.Work.WilG4c.EngineDefs
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4a.affine_comb_defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG GraphComp

/-! ## 1. The base-point map `(l,u) ↦ Fin.append l (χ l u)` -/

/-- The base-point map of the per-cell engine: `(l,u) ↦ Fin.append l (χ l u)`.  Its first `p`
coordinates are the parameters `l` and its last `n` coordinates are the coordinates of
`χ l u`, so that composing the fibre ends with it evaluates them at the base point. -/
def flatMap {p n : ℕ} (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin (p + n) → ℝ) → (Fin (p + n) → ℝ) :=
  fun x => Fin.append (fun i : Fin p => x (Fin.castAdd n i))
    (χ (fun i : Fin p => x (Fin.castAdd n i)) (fun j : Fin n => x (Fin.natAdd p j)))

/-- The parameter coordinates of `flatMap χ` are the first `p` coordinates. -/
@[simp] theorem flatMap_castAdd {p n : ℕ} (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (i : Fin p) (x : Fin (p + n) → ℝ) :
    flatMap χ x (Fin.castAdd n i) = x (Fin.castAdd n i) :=
  Fin.append_left _ _ i

/-- The last `n` coordinates of `flatMap χ` are the coordinates of `χ`, evaluated at the
base point. -/
@[simp] theorem flatMap_natAdd {p n : ℕ} (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (k : Fin n) (x : Fin (p + n) → ℝ) :
    flatMap χ x (Fin.natAdd p k) =
      χ (fun i : Fin p => x (Fin.castAdd n i)) (fun j : Fin n => x (Fin.natAdd p j)) k :=
  Fin.append_right _ _ k

/-! ## 2. Graphs of coordinate projections -/

/-- A coordinate projection has an `Ω`-bounded graph, at format `m+1` and degree `1`, both
independent of the data. -/
theorem graphOf_coord_mw (S : SOMin) (m : ℕ) (i : Fin m) :
    graphOf (fun x : Fin m → ℝ => x i) ∈ S.Ω (m + 1) 1 (m + 1) := by
  have h := Work.WilG1.Omega.coordEq_mem (S := S) 0 (Fin.last m) (Fin.castSucc i)
  have h1 : (Polynomial.eval 0 (Polynomial.C 1) : ℕ) = 1 := by simp
  rw [h1] at h
  rwa [show {x : Fin (m + 1) → ℝ | x (Fin.last m) = x (Fin.castSucc i)} =
      graphOf (fun x : Fin m → ℝ => x i) from rfl] at h

/-! ## 3. The composition step, with explicit increments -/

/-- The format increment of the composition step `compExp`. -/
def compKc (m : ℕ) : ℕ :=
  2 * (((m + 1) + m) + (m + 1)) + 1 + 1 + 1 + m + (m + 1)

/-- **Composition of `Ω`-bounded graphs, with explicit increments.**  If `graphOf g` and the
coordinate graphs of `φ : ℝ^m → ℝ^m` are `Ω`-bounded, then `graphOf (g ∘ φ)` is `Ω`-bounded at
format `F₁ + F₂ + compKc m` and degree `D₁ + 2 + m * (D₂ + 2)`.

This is `Work.WilG4c.GraphOfComp`, whose construction (pull the graph of `g` back to the
coordinates `(w, t)`, pull the coordinate graphs of `φ` back to `(x, w_j)`, intersect and project
the `w`-block away) is repeated verbatim, but with the existential increments of that lemma
replaced by the explicit terms appearing in its proof: those increments are functions of `m`
alone, and exhibiting them is what makes the format/degree bounds below uniform in `D`. -/
theorem compExp (S : SOMin) (m F₁ F₂ D₁ D₂ : ℕ) (g : (Fin m → ℝ) → ℝ)
    (φ : (Fin m → ℝ) → (Fin m → ℝ))
    (hg : graphOf g ∈ S.Ω F₁ D₁ (m + 1))
    (hφ : ∀ j : Fin m, graphOf (fun x : Fin m → ℝ => φ x j) ∈ S.Ω F₂ D₂ (m + 1)) :
    graphOf (g ∘ φ) ∈ S.Ω (F₁ + F₂ + compKc m) (D₁ + 2 + m * (D₂ + 2)) (m + 1) := by
  have hG : setG m g ∈ S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1))
      (D₁ + 2) ((m + 1) + m) :=
    Work.WilG1.Omega.mono (subst_mem S (sigG m) hg) (by omega) le_rfl
  have hH : ∀ j : Fin m, setH m φ j ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1)) (D₂ + 2) ((m + 1) + m) :=
    fun j => Work.WilG1.Omega.mono (subst_mem S (sigPhi m j) (hφ j)) (by omega) le_rfl
  have hA2 : (⋂ j : Fin m, setH m φ j) ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1) (m * (D₂ + 2))
        ((m + 1) + m) := by
    have h := S.inter (F := F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1))
      (n := (m + 1) + m) (D := fun _ : Fin m => D₂ + 2)
      (A := fun j : Fin m => setH m φ j) hH
    have hsum : (∑ _ : Fin m, (D₂ + 2)) = m * (D₂ + 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    rwa [hsum] at h
  have hG' : setG m g ∈ S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1)
      (D₁ + 2) ((m + 1) + m) :=
    Work.WilG1.Omega.mono hG (by omega) le_rfl
  have hInt : (setG m g ∩ ⋂ j : Fin m, setH m φ j) ∈
      S.Ω (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1)
        ((D₁ + 2) + m * (D₂ + 2)) ((m + 1) + m) :=
    Work.WilG0.Omega_inter2 hG' hA2
  have hProj : Work.WilG0.projLastIter (m + 1) m (setG m g ∩ ⋂ j : Fin m, setH m φ j) ∈
      S.Ω ((F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1) + m + (m + 1))
        ((D₁ + 2) + m * (D₂ + 2)) (m + 1) :=
    Work.WilG0.projLastIter_mem S (m + 1) m
      (F₁ + F₂ + (2 * (((m + 1) + m) + (m + 1)) + 1) + 1 + 1)
      ((D₁ + 2) + m * (D₂ + 2)) _ hInt
  have hset : Work.WilG0.projLastIter (m + 1) m (setG m g ∩ ⋂ j : Fin m, setH m φ j) =
      graphOf (g ∘ φ) := by
    rw [Work.WilG0.projLastIter_eq]
    ext x
    constructor
    · rintro ⟨w, hw⟩
      rw [Set.mem_inter_iff] at hw
      obtain ⟨hGm, hHm⟩ := hw
      rw [Set.mem_iInter] at hHm
      have hlast : x (Fin.last m) = g w := (mem_setG g x w).mp hGm
      have hwx : w = φ (Fin.init x) := by
        funext j
        exact (mem_setH φ j x w).mp (hHm j)
      rw [hwx] at hlast
      simpa [graphOf] using hlast
    · intro hx
      have hx' : x (Fin.last m) = g (φ (Fin.init x)) := by simpa [graphOf] using hx
      refine ⟨φ (Fin.init x), ?_⟩
      rw [Set.mem_inter_iff, Set.mem_iInter]
      exact ⟨(mem_setG g x (φ (Fin.init x))).mpr hx',
        fun j => (mem_setH φ j x (φ (Fin.init x))).mpr rfl⟩
  rw [← hset]
  refine Work.WilG1.Omega.mono hProj ?_ (by omega)
  unfold compKc
  omega

/-! ## 4. The affine-combination step, with an explicit degree -/

/-- **Affine combinations of two `Ω`-bounded graphs, with an explicit degree.**  This is
`Work.WilG4a.affine_comb_graph_mem` with its two-variable degree polynomial `Work.WilG4a.bpoly`
replaced by its value `2 * D + (4 * (m + 3) + 9)` (`Work.WilG4a.bpoly_eval`), so that the degree
bound can be used as a closed term uniform in the data. -/
theorem affCombExp (S : SOMin) (m F D : ℕ) (lo hi : (Fin m → ℝ) → ℝ) (c₁ c₂ c₃ : ℝ)
    (hlo : graphOf lo ∈ S.Ω F D (m + 1)) (hhi : graphOf hi ∈ S.Ω F D (m + 1)) :
    graphOf (fun l => c₁ + c₂ * lo l + c₃ * hi l) ∈
      S.Ω (Work.WilG4a.omegaFmt m F + 4) (2 * D + (4 * (m + 3) + 9)) (m + 1) := by
  have hSA : Work.WilG4a.SA m (graphOf lo) ∈
      S.Ω (Work.WilG4a.omegaFmt m F) (Work.WilG4a.omegaDeg m D) (m + 3) :=
    Work.WilG4a.SA_mem hlo
  have hSB : Work.WilG4a.SB m (graphOf hi) ∈
      S.Ω (Work.WilG4a.omegaFmt m F) (Work.WilG4a.omegaDeg m D) (m + 3) :=
    Work.WilG4a.SB_mem hhi
  have hSeq : Work.WilG4a.Seq m c₁ c₂ c₃ ∈ S.Ω (Work.WilG4a.omegaFmt m F) 1 (m + 3) :=
    Work.WilG4a.Seq_mem (S := S) m F c₁ c₂ c₃
  have hSeq' : Work.WilG4a.Seq m c₁ c₂ c₃ ∈ S.Ω (Work.WilG4a.omegaFmt m F + 1) 1 (m + 3) :=
    Work.WilG5.mem_mono hSeq (Work.WilG4a.omegaFmt m F + 1) 1 (by omega) le_rfl
  have hInter : (Work.WilG4a.SA m (graphOf lo) ∩ Work.WilG4a.SB m (graphOf hi) ∩
      Work.WilG4a.Seq m c₁ c₂ c₃) ∈
      S.Ω (Work.WilG4a.omegaFmt m F + 2)
        (Work.WilG4a.omegaDeg m D + Work.WilG4a.omegaDeg m D + 1) (m + 3) :=
    Work.WilG4a.inter_mem (Work.WilG4a.inter_mem hSA hSB) hSeq'
  have hProj : Work.WilG5.projN (n := m + 1) 2
      (Work.WilG4a.SA m (graphOf lo) ∩ Work.WilG4a.SB m (graphOf hi) ∩
        Work.WilG4a.Seq m c₁ c₂ c₃) ∈
      S.Ω (Work.WilG4a.omegaFmt m F + 4)
        (Work.WilG4a.omegaDeg m D + Work.WilG4a.omegaDeg m D + 1) (m + 1) := by
    have h := Work.WilG5.projN_mem (S := S) (n := m + 1) 2 (Work.WilG4a.omegaFmt m F + 2)
      (Work.WilG4a.omegaDeg m D + Work.WilG4a.omegaDeg m D + 1) hInter
    exact Work.WilG5.mem_mono h (Work.WilG4a.omegaFmt m F + 4) _ (by omega) le_rfl
  have hSeqset : Work.WilG4a.Seq m c₁ c₂ c₃ = {z : Fin (m + 3) → ℝ |
      z (Work.WilG4a.yIdx m) = c₁ + c₂ * z (Work.WilG4a.uIdx m) +
        c₃ * z (Work.WilG4a.vIdx m)} := rfl
  rw [Work.WilG4a.sa_char m lo, Work.WilG4a.sb_char m hi, hSeqset,
    Work.WilG4a.proj_comb_eq m lo hi c₁ c₂ c₃] at hProj
  refine Work.WilG5.mem_mono hProj _ (2 * D + (4 * (m + 3) + 9)) le_rfl ?_
  simp only [Work.WilG4a.omegaDeg]
  omega

/-! ## 5. The uniform bounds and the main statement -/

/-- The format contributed by the affine-combination step. -/
def midF1 (p n F0 : ℕ) : ℕ := Work.WilG4a.omegaFmt (p + n) F0 + 4

/-- The format of the coordinate graphs of the base-point map `flatMap χ`. -/
def midF2 (p n F0 : ℕ) : ℕ := max (p + n + 1) F0

/-- The format contributed by the composition step. -/
def midKc (p n : ℕ) : ℕ := compKc (p + n)

/-- The total format gain `A` of `MidWidMem`. -/
def midA (p n F0 : ℕ) : ℕ := midF1 p n F0 + midF2 p n F0 + midKc p n

/-- The degree multiplier `C` of `MidWidMem`. -/
def midC (p n : ℕ) : ℕ := 8 * (p + n) + 25

/-- The midpoint and the shifted half-width of the fibre ends of a cell, evaluated at the base
point `(l, χ l u)`, have `Ω`-bounded graphs whenever `lo`, `hi` and the coordinates of `χ` do.
The format gain and the degree multiplier are uniform in the data. -/
theorem MidWidMem (S : SOMin) (p n F0 : ℕ) : ∃ (A C : ℕ),
    ∀ (D : ℕ) (lo hi : (Fin (p + n) → ℝ) → ℝ)
      (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)),
      graphOf lo ∈ S.Ω F0 D (p + n + 1) →
      graphOf hi ∈ S.Ω F0 D (p + n + 1) →
      (∀ j : Fin n, famGraph (fun l u => χ l u j) ∈ S.Ω F0 D (p + n + 1)) →
      famGraph (Work.WilG4c.midFun lo hi χ) ∈ S.Ω (F0 + A) (C * D + C) (p + n + 1) ∧
      famGraph (Work.WilG4c.widFun lo hi χ) ∈ S.Ω (F0 + A) (C * D + C) (p + n + 1) := by
  refine ⟨midA p n F0, midC p n, ?_⟩
  intro D lo hi χ hlo hhi hχ
  -- the degree produced by the composition is affine in `D` with multiplier `midC p n`
  have hdeg : 2 * D + (4 * ((p + n) + 3) + 9) + 2 + (p + n) * (max 1 D + 2) ≤
      midC p n * D + midC p n := by
    have h2 : (p + n) * (max 1 D + 2) ≤ (p + n) * D + 3 * (p + n) := by
      calc (p + n) * (max 1 D + 2) ≤ (p + n) * (D + 1 + 2) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = (p + n) * D + 3 * (p + n) := by ring
    have hC1 : (p + n + 2) * D ≤ midC p n * D := by
      unfold midC
      exact Nat.mul_le_mul_right D (by omega)
    have hC2 : 7 * (p + n) + 23 ≤ midC p n := by
      unfold midC
      omega
    have e2 : 2 * D + (4 * ((p + n) + 3) + 9) + 2 + (p + n) * (max 1 D + 2) ≤
        (p + n + 2) * D + (7 * (p + n) + 23) := by
      have e1 : (p + n + 2) * D = (p + n) * D + 2 * D := by ring
      rw [e1]
      omega
    omega
  have hfmt : midF1 p n F0 + midF2 p n F0 + midKc p n ≤ F0 + midA p n F0 := by
    unfold midA
    omega
  -- one affine combination of the fibre ends, composed with the base-point map
  have step : ∀ c₁ c₂ c₃ : ℝ,
      famGraph (fun l u =>
          c₁ + c₂ * lo (Fin.append l (χ l u)) + c₃ * hi (Fin.append l (χ l u))) ∈
        S.Ω (F0 + midA p n F0) (midC p n * D + midC p n) (p + n + 1) := by
    intro c₁ c₂ c₃
    have hg : graphOf (fun w : Fin (p + n) → ℝ => c₁ + c₂ * lo w + c₃ * hi w) ∈
        S.Ω (midF1 p n F0) (2 * D + (4 * ((p + n) + 3) + 9)) (p + n + 1) :=
      affCombExp S (p + n) F0 D lo hi c₁ c₂ c₃ hlo hhi
    have hφ : ∀ j : Fin (p + n), graphOf (fun x : Fin (p + n) → ℝ => flatMap χ x j) ∈
        S.Ω (midF2 p n F0) (max 1 D) (p + n + 1) := by
      intro j
      induction j using Fin.addCases with
      | left i =>
        have h := graphOf_coord_mw S (p + n) (Fin.castAdd n i)
        have hf : (fun x : Fin (p + n) → ℝ => flatMap χ x (Fin.castAdd n i)) =
            (fun x : Fin (p + n) → ℝ => x (Fin.castAdd n i)) := by
          funext x
          rw [flatMap_castAdd]
        rw [hf]
        exact Work.WilG1.Omega.mono h (le_max_left (p + n + 1) F0) (le_max_left 1 D)
      | right k =>
        have h := hχ k
        have hf : famGraph (fun l u => χ l u k) =
            graphOf (fun x : Fin (p + n) → ℝ => flatMap χ x (Fin.natAdd p k)) := by
          rw [famGraph]
          congr 1
          funext x
          rw [flatMap_natAdd]
        rw [hf] at h
        exact Work.WilG1.Omega.mono h (le_max_right (p + n + 1) F0) (le_max_right 1 D)
    have hcomp := compExp S (p + n) (midF1 p n F0) (midF2 p n F0)
      (2 * D + (4 * ((p + n) + 3) + 9)) (max 1 D)
      (fun w : Fin (p + n) → ℝ => c₁ + c₂ * lo w + c₃ * hi w) (flatMap χ) hg hφ
    have hgraph : graphOf ((fun w : Fin (p + n) → ℝ => c₁ + c₂ * lo w + c₃ * hi w) ∘
        flatMap χ) =
        famGraph (fun l u =>
          c₁ + c₂ * lo (Fin.append l (χ l u)) + c₃ * hi (Fin.append l (χ l u))) := by
      rw [famGraph]
      rfl
    rw [hgraph] at hcomp
    exact Work.WilG1.Omega.mono hcomp hfmt hdeg
  constructor
  · have h := step 0 (1 / 2) (1 / 2)
    have hfn : (fun l u =>
        (0 : ℝ) + (1 / 2) * lo (Fin.append l (χ l u)) + (1 / 2) * hi (Fin.append l (χ l u))) =
        midFun lo hi χ := by
      funext l u
      simp only [midFun]
      ring
    rw [← hfn]
    exact h
  · have h := step (1 / 4) (-(1 / 2)) (1 / 2)
    have hfn : (fun l u =>
        (1 / 4 : ℝ) + (-(1 / 2)) * lo (Fin.append l (χ l u)) +
          (1 / 2) * hi (Fin.append l (χ l u))) = widFun lo hi χ := by
      funext l u
      simp only [widFun]
      ring
    rw [← hfn]
    exact h

end Work.WilG4c
