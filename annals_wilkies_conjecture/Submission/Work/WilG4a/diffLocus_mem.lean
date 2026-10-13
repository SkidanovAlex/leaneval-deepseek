/-
  WilG4a — the differentiability locus of a one-variable function whose graph is `Ω`-definable.

  Given `G = graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2`, we must exhibit a *format*
  `a` and a *polynomial* `b` (both depending only on `F`) such that, for every `D` and every
  `g` with `graphOf g ∈ S.Ω F D 2`,

  * `liftR {x | DifferentiableAt ℝ g x} ∈ S.Ω a (b.eval D) 1`, and
  * `{z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∈ S.Ω a (b.eval D) 2`.

  The mathematics is the first-order (`ε`-`δ`) definability of differentiability from the graph
  relation; the bookkeeping has already been carried out in `Submission/Work/WilG1/Plumb/`
  (area G1's "plumbing"), whose `Sset N i f` is *by construction* an `Ω`-set as soon as
  `graphOf f` is one, and whose analytic meaning (`Sset_char`) is the `ε`-`δ` condition of the
  derivative in the coordinate `i`.

  What is *not* available there is the uniformity in the degree parameter `D`: the statement
  `Sset_omega_aux` existentially quantifies `a` and `b` after `D` and `f` have been fixed. The
  proof of that theorem, however, is entirely explicit in the constants, so the same proof
  yields the uniform statement `Sset_omega_uniform` produced below.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG4b.posPoly_mem
import Submission.Work.WilG1.Plumb.junkPartial_mem

set_option maxHeartbeats 1000000

namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

/-- Coordinate evaluation of a `Fin.snoc` at the first coordinate. -/
@[simp] theorem snoc2_zero (z : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 2 → ℝ) 0 = z 0 := by
  rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from Fin.ext rfl, Fin.snoc_castSucc]

/-- Coordinate evaluation of a `Fin.snoc` at the last coordinate. -/
@[simp] theorem snoc2_one (z : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 2 → ℝ) 1 = t := by
  rw [show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last]

section Plumb

open Work.WilG1.Plumb

/-- **Uniformity in the degree of `Sset_omega_aux`.**  For a fixed input format `F` and
dimension `N`, the format and the degree-polynomial witnessing `Ω`-membership of `Sset N i f`
can be chosen independently of the degree parameter `D` and of the function `f`: the format is
the explicit numeral `AFR N F + 1` and the degree is the affine polynomial
`2 * X + (2 * KK N + N * 4 + 80)`.

The proof is that of `Sset_omega_aux`, with the quantifiers `D` and `f` moved outside. -/
theorem Sset_omega_uniform {S : WilkiesDesign.SOMin} {N F : ℕ} (i : Fin N) :
    ∃ a : ℕ, ∃ b : Polynomial ℕ, ∀ (D : ℕ) (f : (Fin N → ℝ) → ℝ),
      graphOf f ∈ S.Ω F D (N + 1) → Sset N i f ∈ S.Ω a (b.eval D) (N + 1) := by
  refine ⟨AFR N F + 1,
    Polynomial.C 2 * Polynomial.X + Polynomial.C (2 * KK N + N * 4 + 80), ?_⟩
  intro D f hf
  have hin : innerSet N i f ∈ S.Ω (AA N F + 1) (DEG0 N D) (bigDim N) :=
    innerSet_mem (S := S) i hf
  have hinc : (innerSet N i f)ᶜ ∈ S.Ω (AA N F + 1 + 1) (DEG0 N D) (bigDim N) := S.compl hin
  have hpj : projYSet N i f ∈ S.Ω (A0 N F) (DEG0 N D) (aDim N) := by
    have h := Work.WilG5.projN_mem (S := S) (n := aDim N) (N + 2) (AA N F + 1 + 1)
      (DEG0 N D) hinc
    have h' := S.compl h
    simpa [projYSet, A0] using h'
  have hposd : posDSet N ∈ S.Ω (A0 N F) 3 (aDim N) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := aDim N) 0
      (MvPolynomial.X (dIdxA N) : MvPolynomial (Fin (aDim N)) ℝ)
    exact Work.WilG1.Omega.mono (by simpa [posDSet] using h) (le_A0_posD N F)
      (by simp [MvPolynomial.totalDegree_X])
  have hI1 : posDSet N ∩ projYSet N i f ∈ S.Ω (A1 N F) (DEG1 N D) (aDim N) := by
    have h := inter_same hposd hpj
    simpa [A1, DEG1] using h
  have hpd : projDSet N i f ∈ S.Ω (A1 N F + 1) (DEG1 N D) (bDim N) := by
    have h := Work.WilG5.projN_mem (S := S) (n := bDim N) 1 (A1 N F) (DEG1 N D) hI1
    simpa [projDSet] using h
  have hpdc : (projDSet N i f)ᶜ ∈ S.Ω (A1 N F + 1 + 1) (DEG1 N D) (bDim N) := S.compl hpd
  have hpse : posESet N ∈ S.Ω (A2 N F) 3 (bDim N) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := bDim N) 0
      (MvPolynomial.X (eIdxB N) : MvPolynomial (Fin (bDim N)) ℝ)
    exact Work.WilG1.Omega.mono (by simpa [posESet] using h) (le_A2_posE N F)
      (by simp [MvPolynomial.totalDegree_X])
  have hpdc' : (projDSet N i f)ᶜ ∈ S.Ω (A2 N F) (DEG1 N D) (bDim N) := by
    simpa [A2] using hpdc
  have hI2 : posESet N ∩ (projDSet N i f)ᶜ ∈ S.Ω (A3 N F) (DEG2 N D) (bDim N) := by
    have h := inter_same hpse hpdc'
    simpa [A3, DEG2] using h
  have hSs : Sset N i f ∈ S.Ω (AFR N F + 1) (DEG2 N D) (N + 1) := by
    have h := Work.WilG5.projN_mem (S := S) (n := N + 1) 1 (A3 N F) (DEG2 N D) hI2
    have h' := S.compl h
    simpa [Sset, AFR] using h'
  have hb : (Polynomial.C 2 * Polynomial.X + Polynomial.C (2 * KK N + N * 4 + 80)).eval D
      = DEG2 N D := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [hb]
  exact hSs

/-- **`Sset` in dimension one is the graph of `HasDerivAt`.**  For `f = (x ↦ g (x 0))` the
slice of `f` in the direction `0` is `g` itself, so `Sset_char` identifies `Sset 1 0 f` with
the set of points `(x, c)` at which `c` is the `ε`-`δ` derivative of `g` at `x`, i.e. with
`{v | HasDerivAt g (v 1) (v 0)}`. -/
theorem Sset_one_eq (g : ℝ → ℝ) :
    Sset 1 (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0))
      = {v : Fin 2 → ℝ | HasDerivAt g (v 1) (v 0)} := by
  rw [Sset_char (n := 0) (i := (0 : Fin 1)) (f := (fun x : Fin 1 → ℝ => g (x 0)))]
  ext v
  simp only [Set.mem_ofPred_eq]
  have hslice : (fun t : ℝ => (fun x : Fin 1 → ℝ => g (x 0))
        (Fin.insertNth (0 : Fin 1) t (Fin.removeNth 0 (Fin.init v)))) = fun t => g t := by
    funext t
    have hy : (Fin.insertNth (0 : Fin 1) t (Fin.removeNth 0 (Fin.init v)) : Fin 1 → ℝ) 0 = t := by
      simp
    simpa using congrArg g hy
  have hinit : ((Fin.init v) : Fin 1 → ℝ) 0 = v 0 := rfl
  have hlast : v (Fin.last 1) = v 1 := rfl
  rw [hslice]
  simp only [hinit, hlast]
  exact (Work.WilG1.Plumb.hasDerivAt_iff_epsDeriv (g := g) (a := v 0) (c := v 1)).symm

end Plumb

/-- The graph of the derivative relation `HasDerivAt` is the set of `(x,y)` with `x` in the
differentiability locus and `y = deriv g x`; its projection onto the first coordinate is the
differentiability locus of `g`. -/
theorem hasDerivAt_graph_id (g : ℝ → ℝ) :
    ({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)}
        = {z : Fin 2 → ℝ | HasDerivAt g (z 1) (z 0)}) ∧
    (projLast {z : Fin 2 → ℝ | HasDerivAt g (z 1) (z 0)}
        = Work.WilG1.liftR {x : ℝ | DifferentiableAt ℝ g x}) := by
  constructor
  · ext z
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hd, hy⟩
      rw [hy]
      exact hd.hasDerivAt
    · intro h
      exact ⟨h.differentiableAt, h.deriv.symm⟩
  · ext x
    constructor
    · intro hx
      simp only [projLast, Set.mem_ofPred_eq] at hx
      obtain ⟨t, ht⟩ := hx
      simp only [Work.WilG1.liftR, Set.mem_ofPred_eq]
      exact Work.WilG1.Plumb.exists_hasDerivAt_iff.mp ⟨t, by simpa using ht⟩
    · intro hx
      simp only [Work.WilG1.liftR, Set.mem_ofPred_eq] at hx
      simp only [projLast, Set.mem_ofPred_eq]
      obtain ⟨t, ht⟩ := Work.WilG1.Plumb.exists_hasDerivAt_iff.mpr hx
      exact ⟨t, by simpa using ht⟩

theorem diffLocus_mem (S : WilkiesDesign.SOMin) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : ℝ → ℝ),
      WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      (Work.WilG1.liftR {x : ℝ | DifferentiableAt ℝ g x} ∈ S.Ω a (b.eval D) 1) ∧
      ({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∈ S.Ω a (b.eval D) 2) := by
  obtain ⟨a₀, b₀, hS⟩ := Sset_omega_uniform (S := S) (N := 1) (F := F) (0 : Fin 1)
  refine ⟨a₀ + 1, b₀, ?_⟩
  intro D g hg
  have hs : Work.WilG1.Plumb.Sset 1 (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0))
      ∈ S.Ω a₀ (b₀.eval D) (1 + 1) := hS D _ hg
  rw [Sset_one_eq g] at hs
  constructor
  · rw [← (hasDerivAt_graph_id g).2]
    exact S.proj hs
  · rw [(hasDerivAt_graph_id g).1]
    exact Work.WilG5.mem_mono hs (a₀ + 1) (b₀.eval D) (by omega) le_rfl

end Work.WilG4a
