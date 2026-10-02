import Mathlib
import Submission.Work.Thom.complexification

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The canonical sum-compatible realification of `ℂ^k` — the D1 cure, at the level it is needed

**Why this module exists (read this before using `rifStd`).**

`Work.Thom.covE {m} : EuclideanSpace ℂ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m))` is
`ContinuousLinearEquiv.ofFinrankEq …`, i.e. an *opaque* `Classical.choice` of an existence
statement, and it is the chart linear equivalence with which the chart class
`Work.Thom.localThomOfChart (realification Z) (2*m) covE …` — hence the top Chern class
(`Work.Thom.chernClass m m Z = eulerClass (realification Z)`) — is built.  Consequences
(documented at length in `Submission/Work/Gen/README.md` SESSION 7 and
`Submission/Work/Whitney/_tcm/REDUCTION.md`):

* `c_j = σ(j) • c_j^{classical}` with `σ(j) =` the orientation sign of `covE j`, and the `σ(j)`
  are *independent* across `j`;
* every *same-index* statement (naturality, stability, vanishing, the determinant trick) is
  `σ`-blind — which is why the whole workspace is consistent with the defect;
* every *cross-rank* statement (the Whitney sum formula, `c₂(L ⊕ M) = c₁L ⌣ c₁M`, `TopClassMul`)
  is *equivalent* to the coherence of the `σ`s;
* the deliverable `Work.Gen.generators8` is *equivalent* to `σ(2) = σ(4) = 1` (see `README.md`
  SESSION 8), hence is **not provable** while `covE` is the opaque choice.

**The cure is a definitional change in the Thom area**: define `covE` (and the `let e` inside
`Work.Thom.localThomOfComplexCover`) to be the *canonical, sum-compatible* realification of this
module, instead of `ContinuousLinearEquiv.ofFinrankEq`.

**The obstacle this module removes.**  The Whitney area *has* such a realification
(`Work.Whitney.rif`, with `Work.Whitney.rif_sum_compatible` proved sorry-free in
`Submission/Work/Whitney/chernClass_whitneySum_top.lean`) — but that file lies *above*
`Work.Thom.thomClassOf` in the import order (the Whitney area imports the Thom chapter), so its
`rif` *cannot* be used to define `Work.Thom.covE` or the `let e` of `localThomOfComplexCover`:
the change would be a circular import.  `Work.Gen.rifStd` below is the *same* realification, but
defined — together with its sum-compatibility — in a module that imports only `Mathlib` and the
low Thom module `Submission.Work.Thom.complexification`.  It can therefore be imported by
`Submission/Work/Thom/thomClassOf.lean` itself, and the cure becomes two definiens:

```lean
-- Submission/Work/Thom/thomClassOf.lean (add the import, then)
let e : EuclideanSpace ℂ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) := Work.Gen.rifStd m
-- Submission/Work/Thom/CovDefs.lean
def covE {m : ℕ} : EuclideanSpace ℂ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
  Work.Gen.rifStd m
```

Both occurrences are `rifStd m`, so the `rfl`-proof `Work.Thom.localThomOfComplexCover_tau_eq`
(which identifies `localThomOfComplexCover`'s data with `CovDefs`'s) survives verbatim.  No
statement of the workspace changes; no proof in the workspace unfolds `covE` (checked), so the
change is invisible to every existing proof except in that it *removes* the sign freedom.

**Conventions.**  `rifStd` is the *interleaved* realification (`e₁, i e₁, e₂, i e₂, …`), i.e. the
canonical orientation of a complex vector space, so the `σ`s above become `σ(j) = 1`; and it is
built recursively so that the sum-compatibility of the last theorem below is the recursion itself.
The real-and-imaginary-parts form of the convention is `reimEquiv : ℂ^k ≅ ℝ^k × ℝ^k`.
-/

namespace Work.Gen

open scoped RealInnerProductSpace

noncomputable section

/-! ## Coordinate formulae for `EuclideanSpace.finAddEquivProd`

(`rfl`-level facts about the canonical coordinate shuffle `Fin n ⊕ Fin m ≃ Fin (n+m)`; copied from
`Submission/Work/Thom/exists_rhoC_compat.lean`, which lies too high in the import order for the cure.)
-/

theorem finAddEquivProd_fst {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (w : EuclideanSpace 𝕜 (Fin (n + m))) (i : Fin n) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)) w).1 i
      = w (finSumFinEquiv (Sum.inl i)) := rfl

theorem finAddEquivProd_snd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (w : EuclideanSpace 𝕜 (Fin (n + m))) (j : Fin m) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)) w).2 j
      = w (finSumFinEquiv (Sum.inr j)) := rfl

/-- The inverse of the coordinate shuffle, on the `inl` coordinates. -/
theorem finAddEquivProd_symm_apply_inl {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (x : EuclideanSpace 𝕜 (Fin n)) (y : EuclideanSpace 𝕜 (Fin m)) (i : Fin n) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y)).ofLp
        (finSumFinEquiv (Sum.inl i)) = x.ofLp i := by
  have h1 := finAddEquivProd_fst (𝕜 := 𝕜) (n := n) (m := m)
      ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y)) i
  have h2 : (((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m))
      ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y))).1).ofLp i
        = x.ofLp i := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
  exact h1.symm.trans h2

/-- The inverse of the coordinate shuffle, on the `inr` coordinates. -/
theorem finAddEquivProd_symm_apply_inr {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (x : EuclideanSpace 𝕜 (Fin n)) (y : EuclideanSpace 𝕜 (Fin m)) (j : Fin m) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y)).ofLp
        (finSumFinEquiv (Sum.inr j)) = y.ofLp j := by
  have h1 := finAddEquivProd_snd (𝕜 := 𝕜) (n := n) (m := m)
      ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y)) j
  have h2 : (((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m))
      ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y))).2).ofLp j
        = y.ofLp j := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
  exact h1.symm.trans h2

/-! ## The explicit splittings -/

/-- **The explicit splitting `ℂ^{m₁} × ℂ^{m₂} ≃L[ℂ] ℂ^{m₁+m₂}`** (coordinate concatenation). -/
noncomputable def rifSumC (m₁ m₂ : ℕ) :
    (EuclideanSpace ℂ (Fin m₁) × EuclideanSpace ℂ (Fin m₂)) ≃L[ℂ]
      EuclideanSpace ℂ (Fin (m₁ + m₂)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := m₁) (m := m₂)).symm

/-- **The explicit splitting `ℝ^{k₁} × ℝ^{k₂} ≃L[ℝ] ℝ^{k₁+k₂}`**. -/
noncomputable def rifSumR (k₁ k₂ : ℕ) :
    (EuclideanSpace ℝ (Fin k₁) × EuclideanSpace ℝ (Fin k₂)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (k₁ + k₂)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k₁) (m := k₂)).symm

/-! ## The canonical sum-compatible realification -/

/-- The real-and-imaginary-parts isomorphism `ℂ^k ≅ ℝ^k × ℝ^k`. -/
noncomputable def reimEquiv (k : ℕ) :
    EuclideanSpace ℂ (Fin k) ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
  (LinearEquiv.ofBijective ((Work.Thom.cxRePart (k := k)).prod (Work.Thom.cxImPart (k := k)))
    ⟨fun x y h => by
      have h1 : Work.Thom.cxRePart x = Work.Thom.cxRePart y := congrArg Prod.fst h
      have h2 : Work.Thom.cxImPart x = Work.Thom.cxImPart y := congrArg Prod.snd h
      rw [← Work.Thom.cxOfReal_cxRePart_add_cxMulI_cxImPart x,
        ← Work.Thom.cxOfReal_cxRePart_add_cxMulI_cxImPart y, h1, h2],
     fun p => ⟨Work.Thom.cxOfReal p.1 + Work.Thom.cxMulI (Work.Thom.cxOfReal p.2), by
      refine Prod.ext ?_ ?_
      · simp [LinearMap.prod_apply]
      · simp [LinearMap.prod_apply]⟩⟩).toContinuousLinearEquiv

@[simp] theorem reimEquiv_apply (k : ℕ) (z : EuclideanSpace ℂ (Fin k)) :
    reimEquiv k z = (Work.Thom.cxRePart z, Work.Thom.cxImPart z) := rfl

/-- The product of two continuous linear equivalences, on a product space. -/
noncomputable def cleProd {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (e₁ : E₁ ≃L[ℝ] F₁) (e₂ : E₂ ≃L[ℝ] F₂) : (E₁ × E₂) ≃L[ℝ] (F₁ × F₂) where
  toFun p := (e₁ p.1, e₂ p.2)
  invFun q := (e₁.symm q.1, e₂.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_add' p q := by simp [Prod.ext_iff]
  map_smul' c p := by simp [Prod.ext_iff]
  continuous_toFun := (e₁.continuous.comp continuous_fst).prodMk (e₂.continuous.comp continuous_snd)
  continuous_invFun := (e₁.symm.continuous.comp continuous_fst).prodMk
    (e₂.symm.continuous.comp continuous_snd)

@[simp] theorem cleProd_apply {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (e₁ : E₁ ≃L[ℝ] F₁) (e₂ : E₂ ≃L[ℝ] F₂) (p : E₁ × E₂) :
    cleProd e₁ e₂ p = (e₁ p.1, e₂ p.2) := rfl

/-- The rank-one base case of the canonical realification: `ℂ^1 ≅ ℝ^2` by `z ↦ (re z, im z)`. -/
noncomputable def rifOne : EuclideanSpace ℂ (Fin 1) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (reimEquiv 1).trans (rifSumR 1 1)

/-- **The canonical sum-compatible realification** of `ℂ^k` (interleaved real and imaginary parts,
built by peeling the last complex coordinate).  `rifStd k` is the realification that the Thom area
must adopt for `Work.Thom.covE` — see the module docstring. -/
noncomputable def rifStd : (k : ℕ) → EuclideanSpace ℂ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * k))
  | 0 => (reimEquiv 0).trans (rifSumR 0 0)
  | k + 1 => (Nat.mul_succ 2 k) ▸
      ((((rifSumC k 1).symm.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv).trans
        ((cleProd (rifStd k) rifOne).trans (rifSumR (2 * k) 2)))

/-! ## The sum-compatibility of `rifStd`

(The same proof as `Work.Whitney.rif_sum_compatible`, at the level below `Work.Thom.thomClassOf`
where it is needed for the cure.  See `Submission/Work/Whitney/chernClass_whitneySum_top.lean`.)
-/

/-- **The "zip" identity of the explicit complex splitting**: the concatenation of the three blocks
`x`, `y`, `w` is associative, in the form in which the recursion of `rifStd` needs it. -/
theorem rifSumC_zip (m n : ℕ) (x : EuclideanSpace ℂ (Fin m))
    (y : EuclideanSpace ℂ (Fin n)) (w : EuclideanSpace ℂ (Fin 1)) :
    rifSumC m (n + 1) (x, rifSumC n 1 (y, w))
      = rifSumC (m + n) 1 (rifSumC m n (x, y), w) := by
  apply PiLp.ext
  intro k
  rcases (@finSumFinEquiv m (n + 1)).surjective k with ⟨s, rfl⟩
  rcases s with i | j
  · have I1 : (@finSumFinEquiv m (n + 1) (Sum.inl i) : Fin ((m + n) + 1))
        = (@finSumFinEquiv (m + n) 1 (Sum.inl (@finSumFinEquiv m n (Sum.inl i)))) := by
      simp only [finSumFinEquiv_apply_left]
      exact Fin.ext rfl
    rw [show ((rifSumC m (n + 1)) (x, (rifSumC n 1) (y, w))).ofLp
          (finSumFinEquiv (Sum.inl i)) = x.ofLp i from
        finAddEquivProd_symm_apply_inl x ((rifSumC n 1) (y, w)) i]
    rw [I1]
    rw [show ((rifSumC (m + n) 1) ((rifSumC m n) (x, y), w)).ofLp
          (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))))
        = ((rifSumC m n) (x, y)).ofLp (finSumFinEquiv (Sum.inl i)) from
        finAddEquivProd_symm_apply_inl ((rifSumC m n) (x, y)) w (finSumFinEquiv (Sum.inl i))]
    rw [show ((rifSumC m n) (x, y)).ofLp (finSumFinEquiv (Sum.inl i)) = x.ofLp i from
        finAddEquivProd_symm_apply_inl x y i]
  · rcases (@finSumFinEquiv n 1).surjective j with ⟨t, rfl⟩
    rcases t with i' | l
    · have I2 : (@finSumFinEquiv m (n + 1) (Sum.inr (@finSumFinEquiv n 1 (Sum.inl i')))
            : Fin ((m + n) + 1))
          = (@finSumFinEquiv (m + n) 1 (Sum.inl (@finSumFinEquiv m n (Sum.inr i')))) := by
        simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        exact Fin.ext rfl
      rw [show ((rifSumC m (n + 1)) (x, (rifSumC n 1) (y, w))).ofLp
            (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i'))))
          = ((rifSumC n 1) (y, w)).ofLp (finSumFinEquiv (Sum.inl i')) from
          finAddEquivProd_symm_apply_inr x ((rifSumC n 1) (y, w))
            (finSumFinEquiv (Sum.inl i'))]
      rw [show ((rifSumC n 1) (y, w)).ofLp (finSumFinEquiv (Sum.inl i')) = y.ofLp i' from
          finAddEquivProd_symm_apply_inl y w i']
      rw [I2]
      rw [show ((rifSumC (m + n) 1) ((rifSumC m n) (x, y), w)).ofLp
            (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i'))))
          = ((rifSumC m n) (x, y)).ofLp (finSumFinEquiv (Sum.inr i')) from
          finAddEquivProd_symm_apply_inl ((rifSumC m n) (x, y)) w (finSumFinEquiv (Sum.inr i'))]
      rw [show ((rifSumC m n) (x, y)).ofLp (finSumFinEquiv (Sum.inr i')) = y.ofLp i' from
          finAddEquivProd_symm_apply_inr x y i']
    · have I3 : (@finSumFinEquiv m (n + 1) (Sum.inr (@finSumFinEquiv n 1 (Sum.inr l)))
            : Fin ((m + n) + 1)) = (@finSumFinEquiv (m + n) 1 (Sum.inr l)) := by
        simp only [finSumFinEquiv_apply_right, Fin.natAdd]
        exact Fin.ext (by simp only [Fin.natAdd]; omega)
      rw [show ((rifSumC m (n + 1)) (x, (rifSumC n 1) (y, w))).ofLp
            (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr l))))
          = ((rifSumC n 1) (y, w)).ofLp (finSumFinEquiv (Sum.inr l)) from
          finAddEquivProd_symm_apply_inr x ((rifSumC n 1) (y, w))
            (finSumFinEquiv (Sum.inr l))]
      rw [show ((rifSumC n 1) (y, w)).ofLp (finSumFinEquiv (Sum.inr l)) = w.ofLp l from
          finAddEquivProd_symm_apply_inr y w l]
      rw [I3]
      rw [show ((rifSumC (m + n) 1) ((rifSumC m n) (x, y), w)).ofLp
            (finSumFinEquiv (Sum.inr l)) = w.ofLp l from
          finAddEquivProd_symm_apply_inr ((rifSumC m n) (x, y)) w l]

/-- **The "zip" identity of the explicit real splitting** (blocks `2m`, `2n`, `2`). -/
theorem rifSumR_zip (m n : ℕ) (x : EuclideanSpace ℝ (Fin (2 * m)))
    (y : EuclideanSpace ℝ (Fin (2 * n))) (w : EuclideanSpace ℝ (Fin 2)) :
    rifSumR (2 * m) (2 * (n + 1)) (x, rifSumR (2 * n) 2 (y, w))
      = rifSumR (2 * m + 2 * n) 2 (rifSumR (2 * m) (2 * n) (x, y), w) := by
  apply PiLp.ext
  intro k
  rcases (@finSumFinEquiv (2 * m) (2 * (n + 1))).surjective k with ⟨s, rfl⟩
  rcases s with i | j
  · have I1 : (@finSumFinEquiv (2 * m) (2 * (n + 1)) (Sum.inl i)
          : Fin ((2 * m + 2 * n) + 2))
        = (@finSumFinEquiv (2 * m + 2 * n) 2
            (Sum.inl (@finSumFinEquiv (2 * m) (2 * n) (Sum.inl i)))) := by
      simp only [finSumFinEquiv_apply_left]
      exact Fin.ext rfl
    rw [show ((rifSumR (2 * m) (2 * (n + 1))) (x, (rifSumR (2 * n) 2) (y, w))).ofLp
          (finSumFinEquiv (Sum.inl i)) = x.ofLp i from
        finAddEquivProd_symm_apply_inl x ((rifSumR (2 * n) 2) (y, w)) i]
    rw [I1]
    rw [show ((rifSumR (2 * m + 2 * n) 2) ((rifSumR (2 * m) (2 * n)) (x, y), w)).ofLp
          (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))))
        = ((rifSumR (2 * m) (2 * n)) (x, y)).ofLp (finSumFinEquiv (Sum.inl i)) from
        finAddEquivProd_symm_apply_inl ((rifSumR (2 * m) (2 * n)) (x, y)) w
          (finSumFinEquiv (Sum.inl i))]
    rw [show ((rifSumR (2 * m) (2 * n)) (x, y)).ofLp (finSumFinEquiv (Sum.inl i))
          = x.ofLp i from
        finAddEquivProd_symm_apply_inl x y i]
  · rcases (@finSumFinEquiv (2 * n) 2).surjective j with ⟨t, rfl⟩
    rcases t with i' | l
    · have I2 : (@finSumFinEquiv (2 * m) (2 * (n + 1))
            (Sum.inr (@finSumFinEquiv (2 * n) 2 (Sum.inl i'))) : Fin ((2 * m + 2 * n) + 2))
          = (@finSumFinEquiv (2 * m + 2 * n) 2
              (Sum.inl (@finSumFinEquiv (2 * m) (2 * n) (Sum.inr i')))) := by
        simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        exact Fin.ext rfl
      rw [show ((rifSumR (2 * m) (2 * (n + 1))) (x, (rifSumR (2 * n) 2) (y, w))).ofLp
            (@finSumFinEquiv (2 * m) (2 * (n + 1))
              (Sum.inr (@finSumFinEquiv (2 * n) 2 (Sum.inl i'))))
          = ((rifSumR (2 * n) 2) (y, w)).ofLp
              (@finSumFinEquiv (2 * n) 2 (Sum.inl i')) from
          finAddEquivProd_symm_apply_inr x ((rifSumR (2 * n) 2) (y, w))
            (finSumFinEquiv (Sum.inl i'))]
      rw [show ((rifSumR (2 * n) 2) (y, w)).ofLp
            (@finSumFinEquiv (2 * n) 2 (Sum.inl i')) = y.ofLp i' from
          finAddEquivProd_symm_apply_inl y w i']
      rw [I2]
      rw [show ((rifSumR (2 * m + 2 * n) 2) ((rifSumR (2 * m) (2 * n)) (x, y), w)).ofLp
            (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i'))))
          = ((rifSumR (2 * m) (2 * n)) (x, y)).ofLp (finSumFinEquiv (Sum.inr i')) from
          finAddEquivProd_symm_apply_inl ((rifSumR (2 * m) (2 * n)) (x, y)) w
            (finSumFinEquiv (Sum.inr i'))]
      rw [show ((rifSumR (2 * m) (2 * n)) (x, y)).ofLp (finSumFinEquiv (Sum.inr i'))
            = y.ofLp i' from
          finAddEquivProd_symm_apply_inr x y i']
    · have I3 : (@finSumFinEquiv (2 * m) (2 * (n + 1))
            (Sum.inr (@finSumFinEquiv (2 * n) 2 (Sum.inr l))) : Fin ((2 * m + 2 * n) + 2))
          = (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l)) := by
        simp only [finSumFinEquiv_apply_right]
        exact Fin.ext (by simp only [Fin.natAdd]; omega)
      rw [show ((rifSumR (2 * m) (2 * (n + 1))) (x, (rifSumR (2 * n) 2) (y, w))).ofLp
            (@finSumFinEquiv (2 * m) (2 * (n + 1))
              (Sum.inr (@finSumFinEquiv (2 * n) 2 (Sum.inr l))))
          = ((rifSumR (2 * n) 2) (y, w)).ofLp
              (@finSumFinEquiv (2 * n) 2 (Sum.inr l)) from
          finAddEquivProd_symm_apply_inr x ((rifSumR (2 * n) 2) (y, w))
            (finSumFinEquiv (Sum.inr l))]
      rw [show ((rifSumR (2 * n) 2) (y, w)).ofLp
            (@finSumFinEquiv (2 * n) 2 (Sum.inr l)) = w.ofLp l from
          finAddEquivProd_symm_apply_inr y w l]
      rw [I3]
      rw [show ((rifSumR (2 * m + 2 * n) 2) ((rifSumR (2 * m) (2 * n)) (x, y), w)).ofLp
            (finSumFinEquiv (Sum.inr l)) = w.ofLp l from
          finAddEquivProd_symm_apply_inr ((rifSumR (2 * m) (2 * n)) (x, y)) w l]

/-- **The coordinate of a transported element**: casting an element of `ℝ^a` along an equality of
indices only changes the index (`Fin.cast`). -/
theorem cast_apply_ofLp {a b : ℕ} (h : a = b) (x : EuclideanSpace ℝ (Fin a)) (i : Fin b) :
    (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) x).ofLp i
      = x.ofLp (Fin.cast h.symm i) := by
  subst h
  rfl

/-- The degenerate ("second block empty") case of the complex zip. -/
theorem rifSumC_zero (m : ℕ) (x : EuclideanSpace ℂ (Fin m)) (y : EuclideanSpace ℂ (Fin 0)) :
    rifSumC m 0 (x, y) = x := by
  apply PiLp.ext
  intro i
  rw [show (rifSumC m 0 (x, y)).ofLp i = x.ofLp i from
    finAddEquivProd_symm_apply_inl x y i]

/-- The degenerate ("second block empty") case of the real zip. -/
theorem rifSumR_zero (m : ℕ) (x : EuclideanSpace ℝ (Fin (2 * m)))
    (y : EuclideanSpace ℝ (Fin 0)) :
    rifSumR (2 * m) 0 (x, y) = x := by
  apply PiLp.ext
  intro i
  rw [show (rifSumR (2 * m) 0 (x, y)).ofLp i = x.ofLp i from
    finAddEquivProd_symm_apply_inl x y i]

/-- **The index bridge for `rifSumR`**: transporting the result of `rifSumR` along the equality
`2*(m+n) = 2*m + 2*n` (and the transported first block) is the same as computing `rifSumR` in the
second form. -/
theorem rifSumR_cast (m n : ℕ)
    (h : 2 * (m + n) = 2 * m + 2 * n) (h' : 2 * (m + n) + 2 = 2 * m + 2 * n + 2)
    (A : EuclideanSpace ℝ (Fin (2 * (m + n)))) (w : EuclideanSpace ℝ (Fin 2)) :
    cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h')
        (rifSumR (2 * (m + n)) 2 (A, w))
      = rifSumR (2 * m + 2 * n) 2
          (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A, w) := by
  apply PiLp.ext
  intro k
  rcases (@finSumFinEquiv (2 * m + 2 * n) 2).surjective k with ⟨s, rfl⟩
  rcases s with i | l
  · have hk : (Fin.cast h'.symm (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inl i))
          : Fin (2 * (m + n) + 2))
        = (@finSumFinEquiv (2 * (m + n)) 2 (Sum.inl (Fin.cast h.symm i))) := Fin.ext rfl
    rw [show (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h')
          (rifSumR (2 * (m + n)) 2 (A, w))).ofLp
          (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inl i))
        = (rifSumR (2 * (m + n)) 2 (A, w)).ofLp
          (Fin.cast h'.symm (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inl i))) from
      cast_apply_ofLp h' _ _]
    rw [hk]
    rw [show (rifSumR (2 * (m + n)) 2 (A, w)).ofLp
          (@finSumFinEquiv (2 * (m + n)) 2 (Sum.inl (Fin.cast h.symm i)))
        = A.ofLp (Fin.cast h.symm i) from
      finAddEquivProd_symm_apply_inl A w (Fin.cast h.symm i)]
    rw [show (rifSumR (2 * m + 2 * n) 2
          (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A, w)).ofLp
          (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inl i))
        = (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A).ofLp i from
      finAddEquivProd_symm_apply_inl
        (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A) w i]
    exact (cast_apply_ofLp h A i).symm
  · have hk : (Fin.cast h'.symm (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l))
          : Fin (2 * (m + n) + 2))
        = (@finSumFinEquiv (2 * (m + n)) 2 (Sum.inr l)) :=
      Fin.ext (by
        first
          | simp [Fin.natAdd, h]
          | (simp only [finSumFinEquiv_apply_right, Fin.natAdd, h]; rfl)
          | (simp only [finSumFinEquiv_apply_right, Fin.natAdd]; omega))
    rw [show (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h')
          (rifSumR (2 * (m + n)) 2 (A, w))).ofLp
          (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l))
        = (rifSumR (2 * (m + n)) 2 (A, w)).ofLp
          (Fin.cast h'.symm (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l))) from
      cast_apply_ofLp h' _ _]
    rw [hk]
    rw [show (rifSumR (2 * (m + n)) 2 (A, w)).ofLp
          (@finSumFinEquiv (2 * (m + n)) 2 (Sum.inr l)) = w.ofLp l from
      finAddEquivProd_symm_apply_inr A w l]
    rw [show (rifSumR (2 * m + 2 * n) 2
          (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A, w)).ofLp
          (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l)) = w.ofLp l from
      finAddEquivProd_symm_apply_inr
        (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A) w l]

/-- **The unary recursion of `rifStd`** (up to the canonical cast `2*(k+1) = 2*k+2`): peeling the
last complex coordinate. -/
theorem rifStd_succ_apply (k : ℕ) (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin 1)) :
    HEq (rifStd (k + 1) (rifSumC k 1 p))
      (rifSumR (2 * k) 2 (rifStd k p.1, rifOne p.2)) := by
  apply heq_of_eq
  rw [rifStd]
  simp only [ContinuousLinearEquiv.trans_apply, cleProd_apply]
  exact congrArg (fun q : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin 1) =>
      rifSumR (2 * k) 2 (rifStd k q.1, rifOne q.2))
    (ContinuousLinearEquiv.symm_apply_apply (rifSumC k 1) p)

/-- **The sum-compatibility of `rifStd`**, in cast form: `rifStd` turns the complex splitting
`ℂ^{m+n} = ℂ^m ⊕ ℂ^n` into the real splitting `ℝ^{2(m+n)} = ℝ^{2m} ⊕ ℝ^{2n}`. -/
theorem rifStd_sum_compatible_cast (m n : ℕ)
    (x : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n)) :
    cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) (Nat.mul_add 2 m n))
        (rifStd (m + n) (rifSumC m n x))
      = rifSumR (2 * m) (2 * n) (rifStd m x.1, rifStd n x.2) := by
  induction n with
  | zero =>
    have hx : x.2 = 0 := Subsingleton.elim _ _
    rw [hx, rifSumC_zero, rifSumR_zero]
    exact eq_of_heq ((cast_heq _ _).trans (heq_of_eq (rfl : rifStd (m + 0) x.1 = rifStd m x.1)))
  | succ n ih =>
    set p := (rifSumC n 1).symm x.2 with hp
    obtain ⟨y, w⟩ := p
    have hyw : rifSumC n 1 (y, w) = x.2 := by
      rw [hp]; exact (rifSumC n 1).apply_symm_apply x.2
    have hxeq : x = (x.1, rifSumC n 1 (y, w)) := by
      rw [hyw]
    rw [hxeq]
    simp only [Prod.fst, Prod.snd]
    have ih' : cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) (Nat.mul_add 2 m n))
        (rifStd (m + n) (rifSumC m n (x.1, y)))
        = rifSumR (2 * m) (2 * n) (rifStd m x.1, rifStd n y) := by
      simpa using ih (x.1, y)
    rw [rifSumC_zip]
    rw [show rifStd (m + (n + 1)) (rifSumC (m + n) 1 (rifSumC m n (x.1, y), w))
        = rifSumR (2 * (m + n)) 2 (rifStd (m + n) (rifSumC m n (x.1, y)), rifOne w) from
      eq_of_heq (rifStd_succ_apply (m + n) (rifSumC m n (x.1, y), w))]
    rw [rifSumR_cast m n (Nat.mul_add 2 m n) (Nat.mul_add 2 m (n + 1))
      (rifStd (m + n) (rifSumC m n (x.1, y))) (rifOne w)]
    rw [show rifStd (n + 1) (rifSumC n 1 (y, w))
        = rifSumR (2 * n) 2 (rifStd n y, rifOne w) from
      eq_of_heq (rifStd_succ_apply n (y, w))]
    rw [rifSumR_zip m n (rifStd m x.1) (rifStd n y) (rifOne w)]
    rw [← ih']

/-- **THE SUM-COMPATIBLE CANONICAL REALIFICATION**: the `HEq` form of
`Work.Gen.rifStd_sum_compatible_cast` (the two sides live in the definitionally unrelated types
`ℝ^{2*(m+n)}` and `ℝ^{2*m+2*n}`, related by `Nat.mul_add`). -/
theorem rifStd_sum_compatible (m n : ℕ)
    (x : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n)) :
    HEq (rifStd (m + n) (rifSumC m n x))
      (rifSumR (2 * m) (2 * n) (rifStd m x.1, rifStd n x.2)) :=
  (cast_heq (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) (Nat.mul_add 2 m n))
    (rifStd (m + n) (rifSumC m n x))).symm.trans (heq_of_eq (rifStd_sum_compatible_cast m n x))

end

end Work.Gen
