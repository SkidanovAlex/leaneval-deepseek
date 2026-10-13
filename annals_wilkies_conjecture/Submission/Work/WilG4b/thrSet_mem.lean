import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4b.posPoly_mem
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture

/-!
  Area G4b: the threshold set `thrSet G t = {s | G is C¹ at s and t < |G'(s)|}` of a
  one-variable function is an `Ω`-set of dimension `1`, with format and degree bounded
  uniformly in `t` in terms of the format/degree of the graph of `G`.

  The proof reads `G` as the function `y ↦ G (y 0)` on `ℝ¹`, applies sharp differentiability
  (`S.SharpDeriv`) to get the `Ω`-set that is the graph of `∂₀` over the interior of the `C¹`
  locus, intersects it with the two half-planes `{t < M}` and `{M < -t}` (manufactured from
  hypersurfaces via `posPoly_mem`), and projects out the last coordinate.  The projection is
  exactly `{x | G is C¹ at x 0 and t < |deriv G (x 0)|}` because on `ℝ¹` the partial derivative
  `∂₀` agrees with `deriv`.
-/

/-! ## 1. The `ℝ¹` model of a one-variable function -/

/-- `y ↦ G (y 0)` on `ℝ¹`. -/
def thrDinG (G : ℝ → ℝ) : (Fin 1 → ℝ) → ℝ := fun y => G (y 0)

/-- `ContDiffAt` of `G` at `x 0` is equivalent to `ContDiffAt` of `y ↦ G (y 0)` at `x`. -/
theorem thrContDiffAt_dinG_iff (G : ℝ → ℝ) (x : Fin 1 → ℝ) :
    ContDiffAt ℝ 1 (thrDinG G) x ↔ ContDiffAt ℝ 1 G (x 0) := by
  have he := (ContinuousLinearEquiv.contDiffAt_comp_iff
      (e := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm)
      (f := thrDinG G) (x := x) (n := 1)).symm
  have h1 : (thrDinG G) ∘ ⇑((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm) = G := by
    funext a
    simp [thrDinG]
  have h2 : ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm).symm x = x 0 := by
    show (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) x = x 0
    rw [ContinuousLinearEquiv.coe_funUnique]
    exact congrArg x (Fin.default_eq_zero 1)
  rw [h1, h2] at he
  exact he

/-- The interior of the `C¹` locus of `y ↦ G (y 0)` is described by `ContDiffAt` of `G`. -/
theorem thrMem_interior_c1 (G : ℝ → ℝ) (x : Fin 1 → ℝ) :
    x ∈ interior {z : Fin 1 → ℝ | ContDiffAt ℝ 1 (thrDinG G) z} ↔ ContDiffAt ℝ 1 G (x 0) := by
  rw [mem_interior_iff_mem_nhds]
  constructor
  · intro h
    exact (thrContDiffAt_dinG_iff G x).1 (mem_of_mem_nhds h)
  · intro h
    exact ((thrContDiffAt_dinG_iff G x).2 h).eventually (by simp)

/-- The first-order derivative of `y ↦ G (y 0)` in the direction of the single coordinate
equals `deriv G (x 0)`. -/
theorem thrIteratedFDeriv (G : ℝ → ℝ) (x : Fin 1 → ℝ) (h : ContDiffAt ℝ 1 G (x 0)) :
    iteratedFDeriv ℝ 1 (thrDinG G) x (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1)
      = deriv G (x 0) := by
  have key : iteratedFDeriv ℝ 1 (thrDinG G) x (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1)
      = (fderiv ℝ (thrDinG G) x) (Pi.single (0 : Fin 1) 1) := by simp
  rw [key]
  have hG : HasFDerivAt G (fderiv ℝ G (x 0)) (x 0) := h.differentiableAt_one.hasFDerivAt
  have hp_eq : (fun y : Fin 1 → ℝ => y 0)
      = ⇑(ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ) := by
    funext y
    rw [ContinuousLinearMap.proj_apply]
  have hp : HasFDerivAt (fun y : Fin 1 → ℝ => y 0)
      (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ) x := by
    rw [hp_eq]
    exact (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have hcomp : HasFDerivAt (thrDinG G)
      ((fderiv ℝ G (x 0)) ∘SL
        (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ)) x :=
    hG.comp x hp
  rw [hcomp.fderiv]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same]
  exact fderiv_apply_one_eq_deriv

/-! ## 2. Auxiliary `Ω`-sets in `ℝ²` -/

/-- The graph of `∂₀ (y ↦ G (y 0))` over the interior of its `C¹` locus. -/
def thrDeriGraph (G : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  {z | Fin.init z ∈ interior {x : Fin 1 → ℝ | ContDiffAt ℝ 1 (thrDinG G) x} ∧
       z (Fin.last 1) = iteratedFDeriv ℝ 1 (thrDinG G) (Fin.init z)
         (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1)}

/-- The open half-plane `t < M` in `ℝ² = ℝ × ℝ`. -/
def thrPosHalf (t : ℝ) : Set (Fin 2 → ℝ) := {z | t < z (Fin.last 1)}

/-- The open half-plane `M < -t` in `ℝ² = ℝ × ℝ`. -/
def thrNegHalf (t : ℝ) : Set (Fin 2 → ℝ) := {z | z (Fin.last 1) < -t}

/-- The half-plane `t < M` is an `Ω`-set, with a bound depending on nothing. -/
theorem thrPosHalf_mem (S : WilkiesDesign.SOMin) (t : ℝ) :
    thrPosHalf t ∈ S.Ω 6 4 2 := by
  have hmem := posPoly_mem S
    (MvPolynomial.X (Fin.last 1) - MvPolynomial.C t : MvPolynomial (Fin 2) ℝ)
  have hset : {z : Fin 2 → ℝ | 0 < MvPolynomial.eval z
      (MvPolynomial.X (Fin.last 1) - MvPolynomial.C t : MvPolynomial (Fin 2) ℝ)}
      = thrPosHalf t := by
    ext z
    simp only [thrPosHalf, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    constructor <;> intro h <;> linarith
  rw [hset] at hmem
  have htd : (MvPolynomial.X (Fin.last 1) - MvPolynomial.C t : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by
    refine le_trans (Work.WilG5.td_sub_le _ _) (max_le (Work.WilG5.td_X_le _) ?_)
    exact le_trans (Work.WilG5.td_C_le _) (Nat.zero_le 1)
  exact Work.WilG5.mem_mono hmem 6 4 (by omega) (by omega)

/-- The half-plane `M < -t` is an `Ω`-set, with a bound depending on nothing. -/
theorem thrNegHalf_mem (S : WilkiesDesign.SOMin) (t : ℝ) :
    thrNegHalf t ∈ S.Ω 6 4 2 := by
  have hmem := posPoly_mem S
    (MvPolynomial.C (-t) - MvPolynomial.X (Fin.last 1) : MvPolynomial (Fin 2) ℝ)
  have hset : {z : Fin 2 → ℝ | 0 < MvPolynomial.eval z
      (MvPolynomial.C (-t) - MvPolynomial.X (Fin.last 1) : MvPolynomial (Fin 2) ℝ)}
      = thrNegHalf t := by
    ext z
    simp only [thrNegHalf, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    constructor <;> intro h <;> linarith
  rw [hset] at hmem
  have htd : (MvPolynomial.C (-t) - MvPolynomial.X (Fin.last 1) : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by
    refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ (Work.WilG5.td_X_le _))
    exact le_trans (Work.WilG5.td_C_le _) (Nat.zero_le 1)
  exact Work.WilG5.mem_mono hmem 6 4 (by omega) (by omega)

/-! ## 3. The main statement -/

theorem thrSet_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) {F D : ℕ} (G : ℝ → ℝ)
    (hG : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∈ S.Ω F D 2) :
    ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (t : ℝ),
      {x : Fin 1 → ℝ | x 0 ∈ Work.WilG4b.thrSet G t} ∈ S.Ω (F + K) (p.eval D) 1 := by
  obtain ⟨a, b, hb⟩ := hder F 1
  have hDg : thrDeriGraph G ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) 2 :=
    hb D (thrDinG G) hG 1 (fun _ : Fin 1 => 0)
  have hDgp : thrDeriGraph G ∈ S.Ω a (Polynomial.eval D (Work.WilG1.psubst b 1)) 2 := by
    rw [Work.WilG1.eval_psubst]; exact hDg
  have hPos : ∀ t : ℝ, thrPosHalf t ∈ S.Ω 6 4 2 := fun t => thrPosHalf_mem S t
  have hNeg : ∀ t : ℝ, thrNegHalf t ∈ S.Ω 6 4 2 := fun t => thrNegHalf_mem S t
  refine ⟨max a (max 6 6) + 1 + 1,
    Work.WilG1.psubst b 1 + (Polynomial.C 4 + Polynomial.C 4), fun t => ?_⟩
  have hPosc : thrPosHalf t ∈ S.Ω 6 (Polynomial.eval D (Polynomial.C 4)) 2 := by
    rw [Polynomial.eval_C]; exact hPos t
  have hNegc : thrNegHalf t ∈ S.Ω 6 (Polynomial.eval D (Polynomial.C 4)) 2 := by
    rw [Polynomial.eval_C]; exact hNeg t
  have hU : thrPosHalf t ∪ thrNegHalf t ∈
      S.Ω (max 6 6) (Polynomial.eval D (Polynomial.C 4 + Polynomial.C 4)) 2 :=
    Work.WilG1.Omega.union₂ hPosc hNegc
  have hInt : thrDeriGraph G ∩ (thrPosHalf t ∪ thrNegHalf t) ∈
      S.Ω (max a (max 6 6) + 1)
        (Polynomial.eval D (Work.WilG1.psubst b 1 + (Polynomial.C 4 + Polynomial.C 4))) 2 :=
    Work.WilG1.Omega.inter₂ hDgp hU
  have hproj := S.proj hInt
  have hset : projLast (thrDeriGraph G ∩ (thrPosHalf t ∪ thrNegHalf t))
      = {x : Fin 1 → ℝ | x 0 ∈ thrSet G t} := by
    ext x
    constructor
    · rintro ⟨M, hM⟩
      obtain ⟨hDgM, hUM⟩ :=
        (Set.mem_inter_iff (Fin.snoc x M) (thrDeriGraph G) (thrPosHalf t ∪ thrNegHalf t)).mp hM
      simp only [thrDeriGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hDgM
      obtain ⟨hint, hMval⟩ := hDgM
      have hc : ContDiffAt ℝ 1 G (x 0) := (thrMem_interior_c1 G x).1 hint
      have hit := thrIteratedFDeriv G x hc
      have hUM' : t < M ∨ M < -t := by
        rcases (Set.mem_union (Fin.snoc x M) (thrPosHalf t) (thrNegHalf t)).mp hUM with h | h
        · exact Or.inl (by simpa only [thrPosHalf, Set.mem_ofPred_eq, Fin.snoc_last] using h)
        · exact Or.inr (by simpa only [thrNegHalf, Set.mem_ofPred_eq, Fin.snoc_last] using h)
      simp only [thrSet, Set.mem_ofPred_eq]
      refine ⟨hc, ?_⟩
      rw [← hit, ← hMval, lt_abs]
      rcases hUM' with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · intro hx
      simp only [thrSet, Set.mem_ofPred_eq] at hx
      obtain ⟨hc, hlt⟩ := hx
      have hint : x ∈ interior {z : Fin 1 → ℝ | ContDiffAt ℝ 1 (thrDinG G) z} :=
        (thrMem_interior_c1 G x).2 hc
      let M : ℝ := iteratedFDeriv ℝ 1 (thrDinG G) x (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1)
      have hit : M = deriv G (x 0) := thrIteratedFDeriv G x hc
      refine ⟨M, ?_⟩
      refine (Set.mem_inter_iff (Fin.snoc x M) (thrDeriGraph G)
        (thrPosHalf t ∪ thrNegHalf t)).mpr ⟨?_, ?_⟩
      · simp only [thrDeriGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
        exact ⟨hint, rfl⟩
      · refine (Set.mem_union (Fin.snoc x M) (thrPosHalf t) (thrNegHalf t)).mpr ?_
        rcases (lt_abs.mp hlt) with h | h
        · left
          simp only [thrPosHalf, Set.mem_ofPred_eq, Fin.snoc_last]
          rw [hit]; exact h
        · right
          simp only [thrNegHalf, Set.mem_ofPred_eq, Fin.snoc_last]
          rw [hit]; linarith
  rw [hset] at hproj
  exact Work.WilG5.mem_mono hproj (F + (max a (max 6 6) + 1 + 1))
    (Polynomial.eval D (Work.WilG1.psubst b 1 + (Polynomial.C 4 + Polynomial.C 4)))
    (by omega) le_rfl

end Work.WilG4b
