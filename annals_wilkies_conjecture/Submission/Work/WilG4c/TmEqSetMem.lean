import Mathlib
import Submission.Work.WilG4c.SgnEqAbs
import Submission.Work.WilG4c.FDerivDirGraphMem
import Submission.Work.WilG4c.SgnSetMem
import Submission.Work.WilG4c.StepBadLoc
import Submission.Work.WilG4c.PerCellDispatch
import Submission.Work.WilG4c.polyComposeD

set_option autoImplicit false
noncomputable section

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-!  ## Auxiliary material: the `ε`-`δ` derivative relation is `Ω`-definable

`epsFDerivSet N φ` is the set of pairs `(x, c)` of `ℝ^{N+N}` with `fderiv ℝ φ x = linMap c`.
It is realised by a shape of the clash-free shape calculus `PKS`/`fdP` of
`Submission.Work.WilG4c.SliceC1FD`: the atom `fdP` is exactly the pointwise `ε`-`δ`
Fréchet condition with the candidate derivative read off from ambient coordinates, and the
value coordinate is supplied by a `mem` atom and then projected away.

(`Submission.Work.WilG4c.EpsFDerivSetMem` proves the same statement by a different route, but
that module imports `EpsSetDefs`, whose `Work.WilG4c.wIdx` clashes with the one of
`ValSetDefs`; this file must therefore avoid it.) -/
namespace TmEqAux

/-- `Fin.append` into an empty left block is a reindexing by `Fin.cast (Nat.zero_add L)`. -/
theorem append_empty_eq {L : ℕ} (f : Fin 0 → ℝ) (u : Fin L → ℝ) :
    Fin.append f u = u ∘ Fin.cast (Nat.zero_add L) := by
  funext k
  conv_lhs => rw [show k = Fin.natAdd 0 (Fin.cast (Nat.zero_add L) k) from Fin.ext (by simp)]
  rw [Fin.append_right]
  rfl

/-- Reading a glued point in a graph. -/
theorem snoc_mem_graphOf {n : ℕ} (f : (Fin n → ℝ) → ℝ) (a : Fin n → ℝ) (b : ℝ) :
    Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) a b ∈ graphOf f ↔ b = f a := by
  simp [graphOf, Fin.init_snoc]

/-- The coordinate block of the argument, as a function. -/
theorem snoc_comp_iy (L : ℕ) (x : Fin (L + L) → ℝ) (t : ℝ) :
    Fin.snoc (α := fun _ : Fin (L + L + 1) => ℝ) x t ∘
      (fun j : Fin L => Fin.castSucc (Fin.castAdd L j)) = x ∘ Fin.castAdd L := by
  funext j; simp

/-- The empty block of parameters, as a function. -/
theorem snoc_comp_iw (L : ℕ) (x : Fin (L + L) → ℝ) (t : ℝ) :
    Fin.snoc (α := fun _ : Fin (L + L + 1) => ℝ) x t ∘ (fun i : Fin 0 => Fin.elim0 i) =
      (fun _ : Fin 0 => (0 : ℝ)) := by
  funext i; exact Fin.elim0 i

/-- `Fin.append` does not depend on its empty left block. -/
theorem append_zero_congr {L : ℕ} (f : Fin 0 → ℝ) (u : Fin L → ℝ) :
    Fin.append f u = Fin.append (fun _ : Fin 0 => (0 : ℝ)) u := by
  rw [append_empty_eq, append_empty_eq]

/-- The `PKS`-shape realising the pointwise `ε`-`δ` derivative relation of a function whose
graph is `graphOf Ψ`: a `mem` atom pins the value coordinate `z (last (L+L))` to `Ψ` of the
argument block, `fdP` reads the candidate derivative off the last `L` coordinates, and the
value coordinate is projected away. -/
noncomputable def epsShape (S : SOMin) (L F D : ℕ) (G : Set (Fin (0 + L + 1) → ℝ))
    (hG : G ∈ S.Ω F D (0 + L + 1)) : PKS S F D (L + L) :=
  PKS.exi (PKS.conj
    (PKS.mem G hG (memIdx (fun i : Fin 0 => Fin.elim0 i)
      (fun j : Fin L => Fin.castSucc (Fin.castAdd L j))
      (Fin.last (L + L))))
    (fdP S F D G hG (fun i : Fin 0 => Fin.elim0 i)
      (fun j : Fin L => Fin.castSucc (Fin.castAdd L j))
      (fun j : Fin L => Fin.castSucc (Fin.natAdd L j))
      (Fin.last (L + L))))

theorem epsShape_Real (S : SOMin) (L F D : ℕ) (Ψ : (Fin (0 + L) → ℝ) → ℝ)
    (hG : graphOf Ψ ∈ S.Ω F D (0 + L + 1)) :
    (epsShape S L F D (graphOf Ψ) hG).Real =
      {x : Fin (L + L) → ℝ | HasFDerivEps (fun u : Fin L → ℝ =>
        Ψ (Fin.append (fun _ : Fin 0 => (0 : ℝ)) u)) (x ∘ Fin.castAdd L)
          (x ∘ Fin.natAdd L)} := by
  unfold epsShape
  rw [PKS.Real_exi]
  ext x
  simp only [PKS.Real_conj, PKS.Real_mem, fdP_Real, projLast, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  simp only [memIdx_comp, snoc_mem_graphOf, snoc_last', snoc_castSucc', snoc_comp_iy,
    snoc_comp_iw, append_zero_congr]
  constructor
  · rintro ⟨t, ht, hP⟩
    subst ht
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hP ε hε
    exact ⟨δ, hδ, fun y' hy' => by
      obtain ⟨t', ht', hineq⟩ := hδ' y' hy'
      rw [ht'] at hineq
      exact hineq⟩
  · intro h
    refine ⟨Ψ (Fin.append (fun _ : Fin 0 => (0 : ℝ)) (x ∘ Fin.castAdd L)), rfl,
      fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    exact ⟨δ, hδ, fun y' hy' =>
      ⟨Ψ (Fin.append (fun _ : Fin 0 => (0 : ℝ)) y'), rfl, hδ' y' hy'⟩⟩

theorem last_comp_cast {N : ℕ} (h : N + 1 = 0 + N + 1) :
    Fin.cast h (Fin.last N) = (Fin.last (0 + N) : Fin (0 + N + 1)) := by
  apply Fin.ext; simp

theorem init_comp_cast {N : ℕ} (h : N + 1 = 0 + N + 1) (v : Fin (0 + N + 1) → ℝ) :
    Fin.init (v ∘ Fin.cast h) = (Fin.init v) ∘ Fin.cast (Nat.zero_add N).symm := by
  funext i
  apply congrArg v
  apply Fin.ext
  simp

/-- Reindexing: the graph of `u ↦ φ (u ∘ Fin.cast (Nat.zero_add N).symm)` on `ℝ^{0+N}` is the
pullback of the graph of `φ` along `Fin.cast h`. -/
theorem graphOf_reindex (N : ℕ) (h : N + 1 = 0 + N + 1) (φ : (Fin N → ℝ) → ℝ) :
    graphOf (fun u : Fin (0 + N) → ℝ => φ (u ∘ Fin.cast (Nat.zero_add N).symm))
      = {v : Fin (0 + N + 1) → ℝ | v ∘ Fin.cast h ∈ graphOf φ} := by
  ext v
  simp only [graphOf, Set.mem_ofPred_eq, Function.comp_apply]
  rw [last_comp_cast h, init_comp_cast h v]

/-- `Lin` and `linMap` are the same functional. -/
theorem Lin_eq_linMap {N : ℕ} (c : Fin N → ℝ) : Lin c = linMap c := by
  ext y; rw [Lin_apply, linMap_apply]

theorem cast_cast_symm {N : ℕ} (i : Fin N) :
    Fin.cast (Nat.zero_add N) (Fin.cast (Nat.zero_add N).symm i) = i := by
  simp

/-- **The `ε`-`δ` derivative relation is `Ω`-definable.** -/
theorem epsMem (S : SOMin) (N F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) (φ : (Fin N → ℝ) → ℝ),
        graphOf φ ∈ S.Ω F0 D (N + 1) →
        epsFDerivSet N φ ∈ S.Ω a (b.eval D) (N + N) := by
  set F : ℕ := max (F0 + (0 + N + 1)) ((0 + N + 1) + (N + 1)) + 1 + (N + 1) + (0 + N + 1)
    + ((0 + N + 1) + 4) with hF
  have hFle : max (F0 + (0 + N + 1)) ((0 + N + 1) + (N + 1)) + 1 + (N + 1) + (0 + N + 1)
      ≤ F := by
    rw [hF]; omega
  have huniv : (0 + N + 1) + 4 ≤ F := by rw [hF]; omega
  have hu : (Set.univ : Set (Fin (0 + N + 1) → ℝ)) ∈ S.Ω F 4 (0 + N + 1) := by
    have h := Work.WilG5.univ_mem (S := S) (n := 0 + N + 1)
    exact Work.WilG5.mem_mono h F 4 huniv le_rfl
  let dummy : PKS S F 4 (N + N) := epsShape S N F 4 Set.univ hu
  refine ⟨dummy.Fmt, Polynomial.C dummy.Atoms * (Polynomial.X + Polynomial.C 12), ?_⟩
  intro D φ hφ
  have h1 : N + 1 = 0 + N + 1 := by omega
  let Ψ : (Fin (0 + N) → ℝ) → ℝ := fun u => φ (u ∘ Fin.cast (Nat.zero_add N).symm)
  have hGmem : graphOf Ψ ∈ S.Ω F (D + 2) (0 + N + 1) := by
    have hsub := Work.WilG0.substSet_mem (S := S) hφ (0 + N + 1) (Fin.cast h1)
    rw [← graphOf_reindex N h1 φ] at hsub
    exact Work.WilG5.mem_mono hsub F (D + 2) hFle le_rfl
  let s : PKS S F (D + 2) (N + N) := epsShape S N F (D + 2) (graphOf Ψ) hGmem
  have hFmt : s.Fmt = dummy.Fmt := rfl
  have hAtoms : s.Atoms = dummy.Atoms := rfl
  have hReal := epsShape_Real S N F (D + 2) Ψ hGmem
  have hfun : (fun u : Fin N → ℝ => Ψ (Fin.append (fun _ : Fin 0 => (0 : ℝ)) u)) = φ := by
    funext u
    show φ ((Fin.append (fun _ : Fin 0 => (0 : ℝ)) u) ∘ Fin.cast (Nat.zero_add N).symm) = φ u
    congr 1
    rw [append_empty_eq]
    funext i
    exact congrArg u (cast_cast_symm i)
  have hset : s.Real = epsFDerivSet N φ := by
    show (epsShape S N F (D + 2) (graphOf Ψ) hGmem).Real = epsFDerivSet N φ
    rw [hReal]
    ext x
    simp only [Set.mem_ofPred_eq, hfun, epsFDerivSet]
    rw [c1RealFD, ← Lin_eq_linMap (x ∘ Fin.natAdd N)]
    exact Iff.rfl
  have hmem := PKS.Real_mem_Omega s
  rw [hFmt, hset] at hmem
  have hDeg : s.Deg ≤ dummy.Atoms * (D + 12) := by
    have h := PKS.Deg_le s
    rw [hAtoms] at h
    exact h.trans (Nat.mul_le_mul_left _ (by omega))
  have hdeg : (Polynomial.C dummy.Atoms * (Polynomial.X + Polynomial.C 12)).eval D
      = dummy.Atoms * (D + 12) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  rw [hdeg]
  exact Work.WilG5.mem_mono hmem dummy.Fmt (dummy.Atoms * (D + 12)) le_rfl hDeg

end TmEqAux

/-- A one-parameter family member `f : ℝ^p → ℝ^1 → ℝ`, read as the function
`z ↦ f (init z) (z (last p))` on `ℝ^{p+1}` occurring in the statement of `TmEqSetMem`. -/
theorem famFun_eq_one (p : ℕ) (f : (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ) :
    famFun f = fun z : Fin (p + 1) → ℝ => f (Fin.init z) (fun _ => z (Fin.last p)) := by
  funext z
  show f (fun i : Fin p => z (Fin.castAdd 1 i)) (fun j : Fin 1 => z (Fin.natAdd p j)) =
    f (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))
  have h1 : (fun i : Fin p => z (Fin.castAdd 1 i)) = Fin.init z := by funext i; rfl
  have h2 : (fun j : Fin 1 => z (Fin.natAdd p j)) = (fun _ : Fin 1 => z (Fin.last p)) := by
    funext j
    exact congrArg z (by apply Fin.ext; simp [Fin.natAdd, Fin.last])
  rw [h1, h2]

/-- The comparison set `{|∂_s T_a| = |∂_s T_b|}` of the *total* directional derivatives of two
members of a one-parameter family is `Ω`-definable with format and degree polynomial
independent of the family.

The total derivative `w ↦ fderiv ℝ φ w e` of a function whose graph is `Ω`-definable is
`Ω`-definable (`FDerivDirGraphMem`, fed by the `ε`-`δ` relation of `TmEqAux.epsMem`), and the
comparison set of two such graphs is `Ω`-definable (`absEqCombine`).  Everything is run with
the degree parameter `Da := eval ![D, r] dT` of the family graph, and the resulting
one-variable degree polynomial is composed with `dT` by `polyComposeD`.

(The hypothesis `hder` is not needed by this route.) -/
theorem TmEqSetMem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (p : ℕ) :
    ∀ (F0 : ℕ) (dT : MvPolynomial (Fin 2) ℕ), ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (ι : Type) [Fintype ι] (D r : ℕ) (T : ι → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ),
        (∀ a, WilkiesDesign.CG.famGraph (T a) ∈
          S.Ω F0 (MvPolynomial.eval ![D, r] dT) (p + 1 + 1)) →
        ∀ a b : ι, {w : Fin (p + 1) → ℝ |
            |(fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                T a (Fin.init z) (fun _ => z (Fin.last p))) w)
              (Pi.single (Fin.last p) 1)|
          = |(fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                T b (Fin.init z) (fun _ => z (Fin.last p))) w)
              (Pi.single (Fin.last p) 1)|} ∈
          S.Ω A (MvPolynomial.eval ![D, r] B) (p + 1) := by
  intro F0 dT
  obtain ⟨a₁, b₁, hEps⟩ := TmEqAux.epsMem S (p + 1) F0
  obtain ⟨K, m, c, hG⟩ := FDerivDirGraphMem S (p + 1) (Pi.single (Fin.last p) 1)
  obtain ⟨K', m', c', hA⟩ := absEqCombine S (p + 1)
  obtain ⟨B₁, hB₁⟩ := polyComposeD b₁ dT
  refine ⟨(a₁ + K) + (a₁ + K) + K',
    MvPolynomial.C (2 * m' * m) * B₁ + MvPolynomial.C (2 * m' * c + c'), ?_⟩
  intro ι _ D r T hT a b
  -- the graph of each family member is `Ω`-definable at degree `eval ![D,r] dT`
  have hfam_a : graphOf (famFun (T a)) ∈ S.Ω F0 (MvPolynomial.eval ![D, r] dT) (p + 1 + 1) := by
    rw [graphOf_famFun]; exact hT a
  have hfam_b : graphOf (famFun (T b)) ∈ S.Ω F0 (MvPolynomial.eval ![D, r] dT) (p + 1 + 1) := by
    rw [graphOf_famFun]; exact hT b
  -- the `ε`-`δ` derivative relation
  have heps_a := hEps (MvPolynomial.eval ![D, r] dT) (famFun (T a)) hfam_a
  have heps_b := hEps (MvPolynomial.eval ![D, r] dT) (famFun (T b)) hfam_b
  -- the graph of the total directional derivative along `e`
  have hdg_a := hG a₁ b₁ (MvPolynomial.eval ![D, r] dT) (famFun (T a)) heps_a
  have hdg_b := hG a₁ b₁ (MvPolynomial.eval ![D, r] dT) (famFun (T b)) heps_b
  -- the comparison set of the two derivative graphs
  have habs := hA (a₁ + K) (a₁ + K) (Polynomial.C m * b₁ + Polynomial.C c)
    (Polynomial.C m * b₁ + Polynomial.C c) (MvPolynomial.eval ![D, r] dT)
    (fun w : Fin (p + 1) → ℝ => fderiv ℝ (famFun (T a)) w (Pi.single (Fin.last p) 1))
    (fun w : Fin (p + 1) → ℝ => fderiv ℝ (famFun (T b)) w (Pi.single (Fin.last p) 1))
    hdg_a hdg_b
  -- read `famFun` back as the family member
  have hset : {w : Fin (p + 1) → ℝ |
        |(fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
            T a (Fin.init z) (fun _ => z (Fin.last p))) w) (Pi.single (Fin.last p) 1)|
        = |(fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
            T b (Fin.init z) (fun _ => z (Fin.last p))) w) (Pi.single (Fin.last p) 1)|}
      = {w : Fin (p + 1) → ℝ |
        |(fun w : Fin (p + 1) → ℝ => fderiv ℝ (famFun (T a)) w (Pi.single (Fin.last p) 1)) w|
        = |(fun w : Fin (p + 1) → ℝ => fderiv ℝ (famFun (T b)) w (Pi.single (Fin.last p) 1)) w|} := by
    rw [← famFun_eq_one p (T a), ← famFun_eq_one p (T b)]
  rw [hset]
  -- degree bookkeeping: compose the one-variable degree polynomial with `dT`
  have hdeg : Polynomial.eval (MvPolynomial.eval ![D, r] dT)
      (Polynomial.C m' * ((Polynomial.C m * b₁ + Polynomial.C c) +
        (Polynomial.C m * b₁ + Polynomial.C c)) + Polynomial.C c')
      = MvPolynomial.eval ![D, r]
        (MvPolynomial.C (2 * m' * m) * B₁ + MvPolynomial.C (2 * m' * c + c')) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
    rw [← hB₁ D r]
    ring
  rw [hdeg] at habs
  exact habs

end Work.WilG4c
