/-
  Area G4b: `StarSet_mem`.

  The augmented choice set `StarSet f c d M ⊆ ℝ^{n+3}` is the set of `(x, y, w, u)` with
  `x ∈ (c,d)`, `y` in the open cube, `w = f(x,y)`, `u ≥ 0`, `|∂₀ f(x,y)| > M (1 + n u)` and
  `|∂_{y_j} f(x,y)| ≤ u` for every `j ≥ 1`.  It is shown to be an `Ω`-set, with format
  `F + K` and degree a polynomial in `D`, whenever `graphOf f ∈ S.Ω F D (n+2)`; `K` and the
  polynomial depend only on `F` and `n` (not on `D`, `f`, `c`, `d`, `M`).

  The existential quantifier over the partial `p = ∂ᵢ f(x,y)` is realised by adding `p` as a
  *fresh last* coordinate of `ℝ^{n+4}` (with `(x,y,w,u)` occupying the first `n+3`
  coordinates), requiring `(x, y, p) ∈ derivGraph f i ⊆ ℝ^{n+2}` through the index map
  `eEig n` (which reads the coordinates `0,…,n` together with the fresh one), and projecting
  the fresh coordinate out with `projLast`.  The helper lemmas of the `Ω`-calculus live in the
  namespace `Work.WilG4b.StarAux` so that they do not collide with the identically-named
  lemmas of the sibling module `Submission.Work.WilG4b.ESet_mem`.
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4b.StarDefs
import Submission.Work.WilG4b.posPoly_mem
import Submission.Work.WilG4b.pullback_mem
import Submission.Work.WilG4b.projCoords_mem
import Submission.Work.WilG4b.uniform_pullback_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture

/-! ## The joint sets of the reduction -/

/-- The pullback of the derivative graph along `eEig`: the points of `ℝ^{n+4}` whose
coordinates `0,…,n` together with the last coordinate form a point of `derivGraph f i`. -/
def EbigA {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (i : Fin (n + 1)) : Set (Fin (n + 4) → ℝ) :=
  {z | z ∘ eEig n ∈ derivGraph f i}

/-- The inequality `M (1 + n u) < |p|` in the joint space. -/
def EbigIn (n : ℕ) (M : ℝ) : Set (Fin (n + 4) → ℝ) :=
  {z | M * (1 + n * z (iU n)) < |z (iP n)|}

/-- The inequality `|p| ≤ u` in the joint space. -/
def EbigIp (n : ℕ) : Set (Fin (n + 4) → ℝ) :=
  {z | |z (iP n)| ≤ z (iU n)}

/-- The joint set of the `∂₀`-partial. -/
def Ebig0 {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (M : ℝ) : Set (Fin (n + 4) → ℝ) :=
  EbigA f 0 ∩ EbigIn n M

/-- The joint set of the `∂_{j}`-partial (`j ≥ 1`). -/
def Ebigj {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (j : Fin n) : Set (Fin (n + 4) → ℝ) :=
  EbigA f j.succ ∩ EbigIp n

/-! ## Description of the projected pieces -/

theorem projLast_Ebig0_eq {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (M : ℝ) :
    projLast (Ebig0 f M) = {v : Fin (n + 3) → ℝ | ∃ w₀ : ℝ,
      Fin.snoc (Fin.init (Fin.init v)) w₀ ∈ derivGraph f 0 ∧
      M * (1 + n * v (Fin.last (n + 2))) < |w₀|} := by
  ext v
  simp only [projLast, Ebig0, EbigA, EbigIn, Set.mem_ofPred_eq, Set.mem_inter_iff,
    snoc_comp_eEig, snoc_iU, snoc_iP]

theorem iInter_projLast_Ebigj_eq {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) :
    (⋂ j : Fin n, projLast (Ebigj f j)) = {v : Fin (n + 3) → ℝ | ∀ j : Fin n, ∃ wj : ℝ,
      Fin.snoc (Fin.init (Fin.init v)) wj ∈ derivGraph f j.succ ∧
        |wj| ≤ v (Fin.last (n + 2))} := by
  ext v
  simp only [Set.mem_iInter, projLast, Ebigj, EbigA, EbigIp, Set.mem_ofPred_eq,
    Set.mem_inter_iff, snoc_comp_eEig, snoc_iP, snoc_iU]

/-! ## Elementary `Ω`-sets of linear polynomial inequalities -/

namespace StarAux

theorem td_C_mul_X_le {N : ℕ} (a : ℝ) (i : Fin N) :
    ((MvPolynomial.C a : MvPolynomial (Fin N) ℝ) * MvPolynomial.X i).totalDegree ≤ 1 := by
  refine le_trans (Work.WilG5.td_mul_le _ _) ?_
  have h1 : (MvPolynomial.C a : MvPolynomial (Fin N) ℝ).totalDegree ≤ 0 :=
    Work.WilG5.td_C_le a
  have h2 : (MvPolynomial.X i : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 :=
    Work.WilG5.td_X_le i
  omega

theorem td_const_add_CmulX_add_CmulX {N : ℕ} (r a b : ℝ) (i j : Fin N) :
    (MvPolynomial.C r + MvPolynomial.C a * MvPolynomial.X i +
      MvPolynomial.C b * MvPolynomial.X j : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · exact le_trans (Work.WilG5.td_C_le r) (Nat.zero_le 1)
    · exact td_C_mul_X_le a i
  · exact td_C_mul_X_le b j

theorem linPos_mem {N : ℕ} (S : SOMin) (D : ℕ) (P : MvPolynomial (Fin N) ℝ)
    (hP : P.totalDegree ≤ 1) :
    {x : Fin N → ℝ | 0 < MvPolynomial.eval x P} ∈ S.Ω (N + 4) ((Polynomial.C 4).eval D) N := by
  simpa using (Work.WilG5.mem_mono (posPoly_mem S P) (N + 4) 4 le_rfl (by omega))

theorem linNonpos_mem {N : ℕ} (S : SOMin) (D : ℕ) (P : MvPolynomial (Fin N) ℝ)
    (hP : P.totalDegree ≤ 1) :
    {x : Fin N → ℝ | MvPolynomial.eval x P ≤ 0} ∈ S.Ω (N + 5) ((Polynomial.C 4).eval D) N := by
  have h := S.compl (linPos_mem S D P hP)
  have he : ({x : Fin N → ℝ | 0 < MvPolynomial.eval x P})ᶜ
      = {x : Fin N → ℝ | MvPolynomial.eval x P ≤ 0} := by
    ext x; simp [not_lt]
  rw [he] at h
  simpa using h

/-- `{x | x i ≤ x j}`. -/
theorem leCoord_mem {N : ℕ} (S : SOMin) (D : ℕ) (i j : Fin N) :
    {x : Fin N → ℝ | x i ≤ x j} ∈ S.Ω (N + 5) ((Polynomial.C 4).eval D) N := by
  have h := linNonpos_mem S D
    (MvPolynomial.C 0 + MvPolynomial.C 1 * MvPolynomial.X i +
      MvPolynomial.C (-1) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)
    (td_const_add_CmulX_add_CmulX 0 1 (-1) i j)
  have hset : {x : Fin N → ℝ |
      MvPolynomial.eval x (MvPolynomial.C 0 + MvPolynomial.C 1 * MvPolynomial.X i +
        MvPolynomial.C (-1) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ) ≤ 0}
      = {x : Fin N → ℝ | x i ≤ x j} := by
    ext x
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  simpa using h

/-- `{x | -x i ≤ x j}`. -/
theorem negLeCoord_mem {N : ℕ} (S : SOMin) (D : ℕ) (i j : Fin N) :
    {x : Fin N → ℝ | -x i ≤ x j} ∈ S.Ω (N + 5) ((Polynomial.C 4).eval D) N := by
  have h := linNonpos_mem S D
    (MvPolynomial.C 0 + MvPolynomial.C (-1) * MvPolynomial.X i +
      MvPolynomial.C (-1) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)
    (td_const_add_CmulX_add_CmulX 0 (-1) (-1) i j)
  have hset : {x : Fin N → ℝ |
      MvPolynomial.eval x (MvPolynomial.C 0 + MvPolynomial.C (-1) * MvPolynomial.X i +
        MvPolynomial.C (-1) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ) ≤ 0}
      = {x : Fin N → ℝ | -x i ≤ x j} := by
    ext x
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  simpa using h

/-- `{x | M (1 + n x j) < |x i|}`. -/
theorem absGt_mem {N : ℕ} (S : SOMin) (D : ℕ) (i j : Fin N) (M : ℝ) (n : ℕ) :
    {x : Fin N → ℝ | M * (1 + n * x j) < |x i|} ∈ S.Ω (N + 4) ((Polynomial.C 8).eval D) N := by
  have h1 : {x : Fin N → ℝ | 0 < MvPolynomial.eval x
      (MvPolynomial.C (-M) + MvPolynomial.C 1 * MvPolynomial.X i +
        MvPolynomial.C (-(M * n)) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)} ∈
      S.Ω (N + 4) ((Polynomial.C 4).eval D) N :=
    linPos_mem S D _ (td_const_add_CmulX_add_CmulX (-M) 1 (-(M * n)) i j)
  have h2 : {x : Fin N → ℝ | 0 < MvPolynomial.eval x
      (MvPolynomial.C (-M) + MvPolynomial.C (-1) * MvPolynomial.X i +
        MvPolynomial.C (-(M * n)) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)} ∈
      S.Ω (N + 4) ((Polynomial.C 4).eval D) N :=
    linPos_mem S D _ (td_const_add_CmulX_add_CmulX (-M) (-1) (-(M * n)) i j)
  have h := Work.WilG1.Omega.union₂ (S := S) h1 h2
  have hset : {x : Fin N → ℝ | 0 < MvPolynomial.eval x
        (MvPolynomial.C (-M) + MvPolynomial.C 1 * MvPolynomial.X i +
          MvPolynomial.C (-(M * n)) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)} ∪
      {x : Fin N → ℝ | 0 < MvPolynomial.eval x
        (MvPolynomial.C (-M) + MvPolynomial.C (-1) * MvPolynomial.X i +
          MvPolynomial.C (-(M * n)) * MvPolynomial.X j : MvPolynomial (Fin N) ℝ)}
      = {x : Fin N → ℝ | M * (1 + n * x j) < |x i|} := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [lt_abs]
    constructor
    · rintro (h | h) <;> [left; right] <;> nlinarith
    · rintro (h | h) <;> [left; right] <;> nlinarith
  rw [hset] at h
  refine Work.WilG5.mem_mono h (N + 4) ((Polynomial.C 8).eval D) (by omega) ?_
  simp

/-- The order-one iterated derivative is the `i`-th directional derivative. -/
theorem dDir_eq {m : ℕ} (f : (Fin m → ℝ) → ℝ) (i : Fin m) (z : Fin m → ℝ) :
    dDir f i z = iteratedFDeriv ℝ 1 f z (fun _ : Fin 1 => Pi.single i 1) := by
  rw [dDir, iteratedFDeriv_one_apply]

/-- `SharpDeriv` at order one: the derivative graphs `derivGraph f i` are `Ω`-sets with
format depending only on `F, m` and degree `b.eval ![D,1]`. -/
theorem derivGraph_mem (S : SOMin) (hder : S.SharpDeriv) (m F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin m → ℝ) → ℝ) (i : Fin m),
        graphOf f ∈ S.Ω F0 D (m + 1) →
          derivGraph f i ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (m + 1) := by
  obtain ⟨a, b, hb⟩ := hder F0 m
  refine ⟨a, b, fun D f i hf => ?_⟩
  have h := hb D f hf 1 (fun _ : Fin 1 => i)
  have hset : derivGraph f i =
      {z : Fin (m + 1) → ℝ | Fin.init z ∈ interior {x | ContDiffAt ℝ 1 f x} ∧
        z (Fin.last m) = iteratedFDeriv ℝ 1 f (Fin.init z) (fun _ : Fin 1 => Pi.single i 1)} := by
    ext z
    simp only [derivGraph, c1Loc, dDir_eq]
  rw [hset]
  exact h

end StarAux

/-! ## The main theorem -/

theorem StarSet_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) {n : ℕ} :
    ∀ F : ℕ, ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.graphOf f ∈ S.Ω F D (n + 1 + 1) →
        ∀ (c d M : ℝ), Work.WilG4b.StarSet f c d M ∈ S.Ω (F + K) (p.eval D) (n + 3) := by
  intro F
  obtain ⟨aDer, bDer, hbDer⟩ := StarAux.derivGraph_mem S hder (n + 1) F
  obtain ⟨K3, p3, h3⟩ := uniform_pullback_mem S (n + 2) (n + 4)
  obtain ⟨K2, p2, h2⟩ := uniform_pullback_mem S n (n + 3)
  let bA : Polynomial ℕ := p3.comp (Work.WilG1.psubst bDer 1)
  let b5 : Polynomial ℕ := bA + Polynomial.C 8
  let b6 : Polynomial ℕ := Polynomial.C n * b5
  let b4 : Polynomial ℕ := Polynomial.C 4
  let b3 : Polynomial ℕ := Polynomial.X
  let b2 : Polynomial ℕ := p2.comp (Polynomial.C (16 * n + 16))
  let b1 : Polynomial ℕ := Polynomial.C 8 + Polynomial.C 8
  let pp : Polynomial ℕ := b1 + (b2 + (b3 + (b4 + (b5 + b6))))
  let Fc : ℕ := max (4 * (n + 3) + 20 + 1)
    (max ((4 * n + 24) + K2)
      (max (F + 1)
        (max (4 * (n + 3) + 16)
          (max (max (aDer + K3) (n + 8) + 2) (max (aDer + K3) (n + 10) + 3)))))
  refine ⟨Fc + 5, pp, ?_⟩
  intro D f hf c d M
  -- the derivative graphs, uniformly in the direction
  have hEA : ∀ i : Fin (n + 1), EbigA f i ∈ S.Ω (aDer + K3) (bA.eval D) (n + 4) := by
    intro i
    have hdi : derivGraph f i ∈ S.Ω aDer ((Work.WilG1.psubst bDer 1).eval D) (n + 2) := by
      rw [Work.WilG1.eval_psubst]
      exact hbDer D f i hf
    have h := h3 (eEig n) aDer ((Work.WilG1.psubst bDer 1).eval D) (derivGraph f i) hdi
    rw [← Polynomial.eval_comp] at h
    exact h
  -- the two inequalities of the joint space
  have hEI : EbigIn n M ∈ S.Ω (n + 8) ((Polynomial.C 8).eval D) (n + 4) :=
    StarAux.absGt_mem (S := S) (N := n + 4) D (iP n) (iU n) M n
  have hEIp : EbigIp n ∈ S.Ω (n + 10) ((Polynomial.C 8).eval D) (n + 4) := by
    have h1 : {z : Fin (n + 4) → ℝ | z (iP n) ≤ z (iU n)} ∈
        S.Ω (n + 4 + 5) ((Polynomial.C 4).eval D) (n + 4) :=
      StarAux.leCoord_mem (S := S) (N := n + 4) D (iP n) (iU n)
    have h2 : {z : Fin (n + 4) → ℝ | -z (iP n) ≤ z (iU n)} ∈
        S.Ω (n + 4 + 5) ((Polynomial.C 4).eval D) (n + 4) :=
      StarAux.negLeCoord_mem (S := S) (N := n + 4) D (iP n) (iU n)
    have h := Work.WilG1.Omega.inter₂ (S := S) h1 h2
    have he : {z : Fin (n + 4) → ℝ | z (iP n) ≤ z (iU n)} ∩
        {z : Fin (n + 4) → ℝ | -z (iP n) ≤ z (iU n)} = EbigIp n := by
      ext z
      simp only [EbigIp, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        rw [abs_le]
        exact ⟨by linarith, h1⟩
      · intro h
        rw [abs_le] at h
        exact ⟨h.2, by linarith⟩
    rw [he] at h
    refine Work.WilG5.mem_mono h (n + 10) ((Polynomial.C 8).eval D) (by omega) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  -- the `∂₀`-joint set and its projection
  have hE0 : Ebig0 f M ∈ S.Ω (max (aDer + K3) (n + 8) + 1) (b5.eval D) (n + 4) :=
    Work.WilG1.Omega.inter₂ (S := S) (hEA 0) hEI
  have hP5 : projLast (Ebig0 f M) ∈
      S.Ω (max (aDer + K3) (n + 8) + 2) (b5.eval D) (n + 3) :=
    S.proj hE0
  -- the `∂_{j}`-joint sets and their projections
  have hEj : ∀ j : Fin n, Ebigj f j ∈
      S.Ω (max (aDer + K3) (n + 10) + 1) (b5.eval D) (n + 4) := fun j =>
    Work.WilG1.Omega.inter₂ (S := S) (hEA j.succ) hEIp
  have hP6j : ∀ j : Fin n, projLast (Ebigj f j) ∈
      S.Ω (max (aDer + K3) (n + 10) + 2) (b5.eval D) (n + 3) := fun j =>
    S.proj (hEj j)
  have hP6 : (⋂ j : Fin n, projLast (Ebigj f j)) ∈
      S.Ω (max (aDer + K3) (n + 10) + 3) (b6.eval D) (n + 3) :=
    Work.WilG1.Omega.inter_mem (S := S) (D := D) (fun j : Fin n => projLast (Ebigj f j)) hP6j
  -- the elementary pieces
  have hP1 : {v : Fin (n + 3) → ℝ | v 0 ∈ Set.Ioo c d} ∈
      S.Ω (max (4 * (n + 3) + 20) (4 * (n + 3) + 20) + 1) (b1.eval D) (n + 3) := by
    have hL : {v : Fin (n + 3) → ℝ | c < v 0} ∈
        S.Ω (4 * (n + 3) + 20) ((Polynomial.C 8).eval D) (n + 3) := by
      simpa using (Work.WilG5.ltSet_mem (S := S) (n := n + 3) (0 : Fin (n + 3)) c)
    have hG : {v : Fin (n + 3) → ℝ | v 0 < d} ∈
        S.Ω (4 * (n + 3) + 20) ((Polynomial.C 8).eval D) (n + 3) := by
      simpa using (Work.WilG5.gtSet_mem (S := S) (n := n + 3) (0 : Fin (n + 3)) d)
    have h := Work.WilG1.Omega.inter₂ (S := S) hL hG
    have he : {v : Fin (n + 3) → ℝ | c < v 0} ∩ {v : Fin (n + 3) → ℝ | v 0 < d}
        = {v : Fin (n + 3) → ℝ | v 0 ∈ Set.Ioo c d} := by
      ext v; simp [Set.mem_Ioo]
    rw [he] at h
    exact h
  have hP2 : {v : Fin (n + 3) → ℝ |
      (fun i : Fin n => v (Fin.castAdd 2 i.succ)) ∈ openCube n} ∈
      S.Ω ((4 * n + 24) + K2) (b2.eval D) (n + 3) := by
    have h := h2 (fun i : Fin n => Fin.castAdd 2 i.succ) (4 * n + 24) (16 * n + 16)
      (openCube n) (Work.WilG5.openCube_mem (S := S) (n := n))
    have hb2 : b2.eval D = p2.eval (16 * n + 16) := by
      simp only [b2, Polynomial.eval_comp, Polynomial.eval_C]
    rw [← hb2] at h
    exact h
  have hP3 : {v : Fin (n + 3) → ℝ | Fin.init v ∈ graphOf f} ∈
      S.Ω (F + 1) (b3.eval D) (n + 3) := by
    have h := S.prod_right hf
    simpa only [b3, Polynomial.eval_X] using h
  have hP4 : {v : Fin (n + 3) → ℝ | 0 ≤ v (Fin.last (n + 2))} ∈
      S.Ω (4 * (n + 3) + 16) (b4.eval D) (n + 3) := by
    simpa only [b4, Polynomial.eval_C] using
      (Work.WilG5.leSet_mem (S := S) (n := n + 3) (Fin.last (n + 2)) (0 : ℝ))
  -- assemble: raise everything to the common format `Fc`
  have hFc1 : max (4 * (n + 3) + 20) (4 * (n + 3) + 20) + 1 ≤ Fc := by simp only [Fc]; omega
  have hFc2 : (4 * n + 24) + K2 ≤ Fc := by simp only [Fc]; omega
  have hFc3 : F + 1 ≤ Fc := by simp only [Fc]; omega
  have hFc4 : 4 * (n + 3) + 16 ≤ Fc := by simp only [Fc]; omega
  have hFc5 : max (aDer + K3) (n + 8) + 2 ≤ Fc := by simp only [Fc]; omega
  have hFc6 : max (aDer + K3) (n + 10) + 3 ≤ Fc := by simp only [Fc]; omega
  have hP1' := Work.WilG5.mem_mono hP1 Fc (b1.eval D) hFc1 le_rfl
  have hP2' := Work.WilG5.mem_mono hP2 Fc (b2.eval D) hFc2 le_rfl
  have hP3' := Work.WilG5.mem_mono hP3 Fc (b3.eval D) hFc3 le_rfl
  have hP4' := Work.WilG5.mem_mono hP4 Fc (b4.eval D) hFc4 le_rfl
  have hP5' := Work.WilG5.mem_mono hP5 Fc (b5.eval D) hFc5 le_rfl
  have hP6' := Work.WilG5.mem_mono hP6 Fc (b6.eval D) hFc6 le_rfl
  have hZ56 := Work.WilG1.Omega.inter₂ (S := S) hP5' hP6'
  have hZ456 := Work.WilG1.Omega.inter₂ (S := S) hP4' hZ56
  have hZ3456 := Work.WilG1.Omega.inter₂ (S := S) hP3' hZ456
  have hZ23456 := Work.WilG1.Omega.inter₂ (S := S) hP2' hZ3456
  have hZ := Work.WilG1.Omega.inter₂ (S := S) hP1' hZ23456
  -- identify the intersection with `StarSet`
  have hStarEq : StarSet f c d M =
      {v : Fin (n + 3) → ℝ | v 0 ∈ Set.Ioo c d} ∩
      ({v : Fin (n + 3) → ℝ | (fun i : Fin n => v (Fin.castAdd 2 i.succ)) ∈ openCube n} ∩
      ({v : Fin (n + 3) → ℝ | Fin.init v ∈ graphOf f} ∩
      ({v : Fin (n + 3) → ℝ | 0 ≤ v (Fin.last (n + 2))} ∩
      (projLast (Ebig0 f M) ∩ (⋂ j : Fin n, projLast (Ebigj f j)))))) := by
    rw [iInter_projLast_Ebigj_eq f, projLast_Ebig0_eq f M]
    ext v
    simp only [StarSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [← hStarEq] at hZ
  exact Work.WilG5.mem_mono hZ (F + (Fc + 5)) (pp.eval D)
    (by dsimp only [Fc]; omega) le_rfl

end Work.WilG4b
