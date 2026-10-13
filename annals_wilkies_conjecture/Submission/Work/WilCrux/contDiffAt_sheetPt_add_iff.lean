import Mathlib
import Submission.Work.WilE9.Ift.AppendCLM
import Submission.Work.WilCrux.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open Work.WilE9.Ift

/-! ## Coordinate linear maps for the sheet parametrisation

`sheetPt e v u` is `Fin.append (v ∘ castAdd n₁) ((Fin.append (v ∘ natAdd m) u) ∘ e)`.  The
building blocks below are the two coordinate projections of `ℝ^{a+b}` and the reindexing of
`ℝ^{n₁+n₂}` along an equivalence. -/

/-- The first `a` coordinates of `x : Fin (a+b) → ℝ`. -/
def restrCLM (a b : ℕ) : (Fin (a + b) → ℝ) →L[ℝ] (Fin a → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin a => ContinuousLinearMap.proj (Fin.castAdd b i)

/-- The last `b` coordinates of `x : Fin (a+b) → ℝ`. -/
def tailCLM (a b : ℕ) : (Fin (a + b) → ℝ) →L[ℝ] (Fin b → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin b => ContinuousLinearMap.proj (Fin.natAdd a i)

/-- Reindexing `x ↦ x ∘ e`. -/
def reindexCLM {p q : ℕ} (e : Fin p ≃ Fin q) : (Fin q → ℝ) →L[ℝ] (Fin p → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin p => ContinuousLinearMap.proj (e i)

@[simp] theorem restrCLM_apply (a b : ℕ) (x : Fin (a + b) → ℝ) (i : Fin a) :
    restrCLM a b x i = x (Fin.castAdd b i) := by
  simp [restrCLM]

@[simp] theorem tailCLM_apply (a b : ℕ) (x : Fin (a + b) → ℝ) (i : Fin b) :
    tailCLM a b x i = x (Fin.natAdd a i) := by
  simp [tailCLM]

@[simp] theorem reindexCLM_apply {p q : ℕ} (e : Fin p ≃ Fin q) (x : Fin q → ℝ) (i : Fin p) :
    reindexCLM e x i = x (e i) := by
  simp [reindexCLM]

/-- Splitting `ℝ^{a+b}` into its two halves and appending them back is the identity. -/
theorem appendCLM_restr_tail (a b : ℕ) (x : Fin (a + b) → ℝ) :
    appendCLM a b (restrCLM a b x, tailCLM a b x) = x := by
  ext s
  refine Fin.addCases (motive := fun s => appendCLM a b (restrCLM a b x, tailCLM a b x) s = x s)
    (fun i => ?_) (fun j => ?_) s
  · rw [appendCLM_apply, Fin.append_left, restrCLM_apply]
  · rw [appendCLM_apply, Fin.append_right, tailCLM_apply]

/-! ## `sheetPt` as a continuous linear map -/

/-- `(v,u) ↦ sheetPt e v u` as a continuous linear map. -/
def sheetPtCLM {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2)) :
    ((Fin (m + n1) → ℝ) × (Fin n2 → ℝ)) →L[ℝ] (Fin (m + N) → ℝ) :=
  (appendCLM m N).comp
    (((restrCLM m n1).comp
        (ContinuousLinearMap.fst ℝ (Fin (m + n1) → ℝ) (Fin n2 → ℝ))).prod
      ((reindexCLM e).comp
        ((appendCLM n1 n2).comp
          (((tailCLM m n1).comp
              (ContinuousLinearMap.fst ℝ (Fin (m + n1) → ℝ) (Fin n2 → ℝ))).prod
            (ContinuousLinearMap.snd ℝ (Fin (m + n1) → ℝ) (Fin n2 → ℝ))))))

/-- The value of `sheetPtCLM`. -/
@[simp] theorem sheetPtCLM_apply {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) :
    sheetPtCLM e (v, u) = sheetPt e v u := by
  simp only [sheetPtCLM, restrCLM, tailCLM, reindexCLM, appendCLM_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, sheetPt]
  rfl

/-! ## Decoding the sheet coordinates of a point of `ℝ^{m+N}` -/

/-- The parameter part `v` of the sheet coordinates of `y`. -/
def ptV {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2)) :
    (Fin (m + N) → ℝ) →L[ℝ] (Fin (m + n1) → ℝ) :=
  (appendCLM m n1).comp
    ((restrCLM m N).prod ((restrCLM n1 n2).comp ((reindexCLM e.symm).comp (tailCLM m N))))

/-- The graph part `u` of the sheet coordinates of `y`. -/
def ptU {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2)) :
    (Fin (m + N) → ℝ) →L[ℝ] (Fin n2 → ℝ) :=
  (tailCLM n1 n2).comp ((reindexCLM e.symm).comp (tailCLM m N))

@[simp] theorem ptV_apply_castAdd {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (y : Fin (m + N) → ℝ) (i : Fin m) :
    ptV e y (Fin.castAdd n1 i) = y (Fin.castAdd N i) := by
  simp [ptV]

@[simp] theorem ptV_apply_natAdd {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (y : Fin (m + N) → ℝ) (k : Fin n1) :
    ptV e y (Fin.natAdd m k) = y (Fin.natAdd m (e.symm (Fin.castAdd n2 k))) := by
  simp [ptV]

@[simp] theorem ptU_apply {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (y : Fin (m + N) → ℝ) (l : Fin n2) :
    ptU e y l = y (Fin.natAdd m (e.symm (Fin.natAdd n1 l))) := by
  simp [ptU]

/-- Decoding is a left inverse of `sheetPt`. -/
theorem ptV_sheetPt {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (w : Fin n2 → ℝ) :
    ptV e (sheetPt e v w) = v := by
  funext i
  refine Fin.addCases (motive := fun i => ptV e (sheetPt e v w) i = v i)
    (fun i' => ?_) (fun k => ?_) i
  · rw [ptV_apply_castAdd, sheetPt_castAdd]
  · rw [ptV_apply_natAdd, sheetPt_natAdd, Equiv.apply_symm_apply, Fin.append_left]

/-- Decoding is a left inverse of `sheetPt`, graph part. -/
theorem ptU_sheetPt {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (w : Fin n2 → ℝ) :
    ptU e (sheetPt e v w) = w := by
  funext l
  rw [ptU_apply, sheetPt_natAdd, Equiv.apply_symm_apply, Fin.append_right]

/-- `sheetPt` is a left inverse of the decoding maps. -/
theorem sheetPt_ptV_ptU {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (y : Fin (m + N) → ℝ) :
    sheetPt e (ptV e y) (ptU e y) = y := by
  have h2 : ∀ s : Fin (n1 + n2),
      (Fin.append (fun k : Fin n1 => ptV e y (Fin.natAdd m k)) (ptU e y)) s
        = y (Fin.natAdd m (e.symm s)) := by
    intro s
    refine Fin.addCases (motive := fun s =>
      (Fin.append (fun k : Fin n1 => ptV e y (Fin.natAdd m k)) (ptU e y)) s
        = y (Fin.natAdd m (e.symm s))) (fun k => ?_) (fun l => ?_) s
    · rw [Fin.append_left, ptV_apply_natAdd]
    · rw [Fin.append_right, ptU_apply]
  have h : (fun j : Fin N =>
      (Fin.append (fun k : Fin n1 => ptV e y (Fin.natAdd m k)) (ptU e y)) (e j))
        = tailCLM m N y := by
    funext j
    rw [h2, Equiv.symm_apply_apply, tailCLM_apply]
  rw [sheetPt, h]
  rw [show (fun i : Fin m => ptV e y (Fin.castAdd n1 i)) = restrCLM m N y from by
    funext i; rw [ptV_apply_castAdd, restrCLM_apply]]
  simpa only [appendCLM_apply] using appendCLM_restr_tail m N y

/-- **Transfer of `ContDiffAt` across the sheared sheet parametrisation.**
With `Φ p = Work.WilCrux.sheetPt e p.1 (φ p.1 + p.2)` (so `Φ (v,u) = sheetPt e v (φ v + u)`) and
`hφ : ContDiffAt ℝ n' φ v`, the map `Φ` is a local `C^{n'}` diffeomorphism at `(v,u)`: its
inverse reads `(v,u)` back off `sheetPt e v u` — `Work.WilCrux.sheetPt` is linear in `(v,u)` and
injective (`Work.WilCrux.sheetPt_injective`, with the coordinate API
`Work.WilCrux.sheetPt_castAdd`, `Work.WilCrux.sheetPt_natAdd`) — and subtracts `φ v`.  Hence `f`
is `C^{n'}` at `sheetPt e v (φ v + u)` iff `f ∘ Φ` is `C^{n'}` at `(v,u)`.

Both inverse identities `Φ ∘ Ψ = id`, `Ψ ∘ Φ = id` for
`Ψ y = (v y, u y - φ (v y))` (where `v y`, `u y` decode the sheet coordinates of `y`) are used;
`LinearMap.pi`/`LinearMap.proj` plus `Fin.addCases` build `v` and `u` as linear maps, and
`ContDiffAt.comp`, `ContDiffAt.congr_of_eventuallyEq`, `contDiffAt_pi` do the rest. -/
theorem contDiffAt_sheetPt_add_iff {m n1 n2 N : ℕ} {n' : WithTop ℕ∞} (e : Fin N ≃ Fin (n1 + n2))
    (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ)) (f : (Fin (m + N) → ℝ) → ℝ)
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) (hφ : ContDiffAt ℝ n' φ v) :
    ContDiffAt ℝ n' f (Work.WilCrux.sheetPt e v (φ v + u)) ↔
      ContDiffAt ℝ n' (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
        f (Work.WilCrux.sheetPt e p.1 (φ p.1 + p.2))) (v, u) := by
  let Φ : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) → (Fin (m + N) → ℝ) :=
    fun p => sheetPt e p.1 (φ p.1 + p.2)
  let Ψ : (Fin (m + N) → ℝ) → (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) :=
    fun y => (ptV e y, ptU e y - φ (ptV e y))
  change ContDiffAt ℝ n' f (Φ (v, u)) ↔ ContDiffAt ℝ n' (fun p => f (Φ p)) (v, u)
  -- `Φ` is `C^{n'}` at `(v,u)`.
  have hΦ : ContDiffAt ℝ n'
      (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => sheetPt e p.1 (φ p.1 + p.2)) (v, u) := by
    have h1 : ContDiffAt ℝ n'
        (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => (p.1, φ p.1 + p.2)) (v, u) := by
      refine ContDiffAt.prodMk ?_ ?_
      · simpa using (ContinuousLinearMap.fst ℝ (Fin (m + n1) → ℝ)
          (Fin n2 → ℝ)).contDiff.contDiffAt
      · refine ContDiffAt.add ?_ ?_
        · have hfst := hφ.comp (v, u)
            ((ContinuousLinearMap.fst ℝ (Fin (m + n1) → ℝ) (Fin n2 → ℝ)).contDiff.contDiffAt)
          exact hfst
        · simpa using (ContinuousLinearMap.snd ℝ (Fin (m + n1) → ℝ)
            (Fin n2 → ℝ)).contDiff.contDiffAt
    have h2 : ContDiffAt ℝ n'
        (fun q : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => sheetPt e q.1 q.2) (v, φ v + u) := by
      have h2' : ContDiffAt ℝ n' (⇑(sheetPtCLM e)) (v, φ v + u) :=
        (sheetPtCLM e).contDiff.contDiffAt
      have heq : (⇑(sheetPtCLM e) : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) → (Fin (m + N) → ℝ))
          = fun q => sheetPt e q.1 q.2 := by
        funext q
        exact sheetPtCLM_apply e q.1 q.2
      rw [heq] at h2'
      exact h2'
    have h3 := h2.comp (v, u) h1
    exact h3
  -- `Ψ` is `C^{n'}` at `Φ (v,u)`.
  have hΨ : ContDiffAt ℝ n'
      (fun y : Fin (m + N) → ℝ => (ptV e y, ptU e y - φ (ptV e y))) (Φ (v, u)) := by
    have hpt : ptV e (Φ (v, u)) = v := ptV_sheetPt e v (φ v + u)
    have hφy : ContDiffAt ℝ n' (fun y : Fin (m + N) → ℝ => φ (ptV e y)) (Φ (v, u)) := by
      have h1 : ContDiffAt ℝ n' φ (ptV e (Φ (v, u))) := by rw [hpt]; exact hφ
      have h2 := h1.comp (Φ (v, u)) ((ptV e).contDiff.contDiffAt)
      exact h2
    refine ContDiffAt.prodMk ?_ ?_
    · simpa using (ptV e).contDiff.contDiffAt (x := Φ (v, u))
    · exact ((ptU e).contDiff.contDiffAt (x := Φ (v, u))).sub hφy
  have hΨΦ : Ψ (Φ (v, u)) = (v, u) := by
    show (ptV e (Φ (v, u)), ptU e (Φ (v, u)) - φ (ptV e (Φ (v, u)))) = (v, u)
    rw [show Φ (v, u) = sheetPt e v (φ v + u) from rfl, ptV_sheetPt, ptU_sheetPt]
    simp
  have hΦΨ : ∀ y : Fin (m + N) → ℝ, Φ (Ψ y) = y := by
    intro y
    show sheetPt e (ptV e y) (φ (ptV e y) + (ptU e y - φ (ptV e y))) = y
    rw [add_sub_cancel, sheetPt_ptV_ptU]
  constructor
  · intro hf
    have h := hf.comp (v, u) hΦ
    exact h
  · intro hg
    have hg' : ContDiffAt ℝ n' (fun p => f (Φ p)) (Ψ (Φ (v, u))) := by
      rw [hΨΦ]; exact hg
    have h := hg'.comp (Φ (v, u)) hΨ
    have heq : ((fun p => f (Φ p)) ∘ Ψ) = f := by
      funext y
      show f (Φ (Ψ y)) = f y
      rw [hΦΨ y]
    rw [heq] at h
    exact h

end Work.WilCrux
