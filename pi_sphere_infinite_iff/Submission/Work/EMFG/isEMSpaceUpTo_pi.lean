import Mathlib
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin

/-!
# Range models `K(A, k)` for dependent products over a finite index type

`Work.Serre.IsEMSpaceUpTo A k hk N X pt` says that `π_k(X, pt) ≃* A` and that `π_i(X, pt)` is
trivial for `i ≠ k` in the range `i < k` or `i ≤ N`.  The file
`Submission/Work/RatHurewicz/isEMSpaceUpTo_pi_fin.lean` shows that a *constant* finite product
`Fin r → X` of such models is again a model of `K(Fin r → A, k)`.

This file removes the constancy of the factors: for any finite index type `ι` and a family of
models `(X i, pt i)` of `K(A i, k)`, the dependent product `(i : ι) → X i` is a model of
`K((i : ι) → A i, k)`.  This is the multi-factor statement needed to package the coefficient
groups `ℤ^r ⊕ F` appearing in the range-model computation of `K(A, k)`.

The proof is the same induction as in the constant case.  The binary product
`Work.RatHurewicz.isEMSpaceUpTo_prod`, transported along the canonical homeomorphism
`(Π j : Fin (r+1), X j) ≃ₜ (Π j : Fin r, X j.succ) × X 0` (`depPiConsHomeo`) and the corresponding
additive equivalence of coefficient groups (`depPiConsAddEquiv`), gives the statement for the index
types `Fin r`; an arbitrary finite `ι` is reduced to `Fin (Fintype.card ι)` through
`Fintype.equivFin`, using `Homeomorph.piCongrLeft` for the spaces and `addEquivPiCongrLeft'` for the
groups.
-/

namespace Work.EMFG

noncomputable section

set_option linter.style.haveILetI false

/-- The canonical homeomorphism reshaping a dependent product over `Fin (r + 1)` as the product of
the first factor with the product over the remaining indices:
`(Π j : Fin (r+1), X j) ≃ₜ (Π j : Fin r, X j.succ) × X 0`. -/
def depPiConsHomeo (r : ℕ) (X : Fin (r + 1) → Type) [∀ j, TopologicalSpace (X j)] :
    ((j : Fin (r + 1)) → X j) ≃ₜ ((j : Fin r) → X (Fin.succ j)) × X 0 where
  toFun f := (fun j => f (Fin.succ j), f 0)
  invFun p := fun j => Fin.cases p.2 p.1 j
  left_inv f := by
    funext j
    refine Fin.cases ?_ ?_ j <;> simp [Fin.cases_zero, Fin.cases_succ]
  right_inv p := by
    obtain ⟨g, x⟩ := p
    refine Prod.ext ?_ ?_
    · funext j; simp [Fin.cases_succ]
    · simp [Fin.cases_zero]
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun j => continuous_apply (Fin.succ j)
    · exact continuous_apply 0
  continuous_invFun := by
    refine continuous_pi fun j => ?_
    induction j using Fin.cases with
    | zero => simpa [Fin.cases_zero] using continuous_snd
    | succ k =>
        simp only [Fin.cases_succ]
        exact (continuous_apply k).comp continuous_fst

/-- The additive equivalence underlying `depPiConsHomeo`:
`(Π j : Fin r, A j.succ) × A 0 ≃+ (Π j : Fin (r+1), A j)`. -/
def depPiConsAddEquiv (r : ℕ) (A : Fin (r + 1) → Type) [∀ j, AddCommGroup (A j)] :
    (((j : Fin r) → A (Fin.succ j)) × A 0) ≃+ ((j : Fin (r + 1)) → A j) where
  toFun p := fun j => Fin.cases p.2 p.1 j
  invFun f := (fun j => f (Fin.succ j), f 0)
  left_inv p := by
    obtain ⟨g, x⟩ := p
    refine Prod.ext ?_ ?_
    · funext j; simp [Fin.cases_succ]
    · simp [Fin.cases_zero]
  right_inv f := by
    funext j
    refine Fin.cases ?_ ?_ j <;> simp [Fin.cases_zero, Fin.cases_succ]
  map_add' p q := by
    funext j
    refine Fin.cases ?_ ?_ j <;> simp [Fin.cases_zero, Fin.cases_succ]

/-- **Dependent finite products of range models over `Fin r`.**  If every factor `(X j, pt j)` is a
range model of `K(A j, k)` through degree `N`, then so is the dependent product
`(j : Fin r) → X j` for the coefficient group `(j : Fin r) → A j`. -/
theorem isEMSpaceUpTo_pi_fin_dep {k N : ℕ} (hk : 0 < k) :
    ∀ (r : ℕ) (A : Fin r → Type) [∀ j, AddCommGroup (A j)]
      (X : Fin r → Type) [∀ j, TopologicalSpace (X j)] (pt : ∀ j, X j),
      (∀ j, Work.Serre.IsEMSpaceUpTo (A j) k hk N (X j) (pt j)) →
      Work.Serre.IsEMSpaceUpTo ((j : Fin r) → A j) k hk N ((j : Fin r) → X j) pt := by
  intro r
  induction r with
  | zero =>
    intro A _ X _ pt _
    haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    haveI hX : Subsingleton ((j : Fin 0) → X j) := ⟨fun f g => funext fun j => j.elim0⟩
    haveI hA : Subsingleton ((j : Fin 0) → A j) := ⟨fun f g => funext fun j => j.elim0⟩
    haveI hpi : Subsingleton (HomotopyGroup (Fin k) ((j : Fin 0) → X j) pt) :=
      Work.RatHurewicz.subsingleton_homotopyGroup_of_subsingleton_type hX pt
    refine ⟨⟨MulEquiv.ofBijective
      (f := (1 : HomotopyGroup (Fin k) ((j : Fin 0) → X j) pt →*
        Multiplicative ((j : Fin 0) → A j)))
      ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨1, Subsingleton.elim _ b⟩⟩⟩,
      fun i hi hc => Work.RatHurewicz.subsingleton_homotopyGroup_of_subsingleton_type hX pt⟩
  | succ r ih =>
    intro A _ X _ pt h
    have hIH : Work.Serre.IsEMSpaceUpTo ((j : Fin r) → A (Fin.succ j)) k hk N
        ((j : Fin r) → X (Fin.succ j)) (fun j => pt (Fin.succ j)) :=
      ih (fun j => A (Fin.succ j)) (fun j => X (Fin.succ j)) (fun j => pt (Fin.succ j))
        (fun j => h (Fin.succ j))
    have h0 : Work.Serre.IsEMSpaceUpTo (A 0) k hk N (X 0) (pt 0) := h 0
    have hprod : Work.Serre.IsEMSpaceUpTo
        (((j : Fin r) → A (Fin.succ j)) × A 0) k hk N
        (((j : Fin r) → X (Fin.succ j)) × X 0) ((fun j => pt (Fin.succ j)), pt 0) :=
      Work.RatHurewicz.isEMSpaceUpTo_prod hk (fun j => pt (Fin.succ j)) (pt 0) hIH h0
    have h1 : Work.Serre.IsEMSpaceUpTo (((j : Fin r) → A (Fin.succ j)) × A 0) k hk N
        ((j : Fin (r + 1)) → X j)
        ((depPiConsHomeo r X).symm ((fun j => pt (Fin.succ j)), pt 0)) :=
      Work.RatHurewicz.isEMSpaceUpTo_of_homeomorph hk (depPiConsHomeo r X).symm
        ((fun j => pt (Fin.succ j)), pt 0) hprod
    have hpt : (depPiConsHomeo r X).symm ((fun j => pt (Fin.succ j)), pt 0) = pt := by
      funext j
      refine Fin.cases ?_ ?_ j <;> simp [depPiConsHomeo, Fin.cases_zero, Fin.cases_succ]
    rw [hpt] at h1
    exact Work.RatHurewicz.isEMSpaceUpTo_of_addEquiv hk pt h1 (depPiConsAddEquiv r A)

/-- `Equiv.piCongrLeft'` as an additive equivalence. -/
def addEquivPiCongrLeft' {ι ι' : Type} (A : ι → Type) [∀ i, AddCommGroup (A i)] (e : ι ≃ ι') :
    ((i : ι) → A i) ≃+ ((i' : ι') → A (e.symm i')) :=
  { Equiv.piCongrLeft' A e with map_add' := fun f g => by funext i'; rfl }

theorem isEMSpaceUpTo_pi {ι : Type} [Fintype ι] {A : ι → Type} [∀ i, AddCommGroup (A i)]
    {k N : ℕ} (hk : 0 < k) {X : ι → Type} [∀ i, TopologicalSpace (X i)] (pt : ∀ i, X i)
    (h : ∀ i, Work.Serre.IsEMSpaceUpTo (A i) k hk N (X i) (pt i)) :
    Work.Serre.IsEMSpaceUpTo ((i : ι) → A i) k hk N ((i : ι) → X i) pt := by
  classical
  set r := Fintype.card ι with hr
  set e : ι ≃ Fin r := Fintype.equivFin ι with he
  have h' : ∀ j : Fin r, Work.Serre.IsEMSpaceUpTo (A (e.symm j)) k hk N
      (X (e.symm j)) (pt (e.symm j)) := fun j => h (e.symm j)
  have hfin : Work.Serre.IsEMSpaceUpTo ((j : Fin r) → A (e.symm j)) k hk N
      ((j : Fin r) → X (e.symm j)) (fun j => pt (e.symm j)) :=
    isEMSpaceUpTo_pi_fin_dep hk r (fun j => A (e.symm j)) (fun j => X (e.symm j))
      (fun j => pt (e.symm j)) h'
  have hhomeo := Work.RatHurewicz.isEMSpaceUpTo_of_homeomorph hk
      (Homeomorph.piCongrLeft (Y := X) e.symm) (fun j => pt (e.symm j)) hfin
  have hpt : Homeomorph.piCongrLeft (Y := X) e.symm (fun j => pt (e.symm j)) = pt := by
    funext i
    have h1 := Homeomorph.piCongrLeft_apply_apply (Y := X) e.symm
      (fun j => pt (e.symm j)) (e i)
    rw [Equiv.symm_apply_apply] at h1
    rw [h1]
  have h2 : Work.Serre.IsEMSpaceUpTo ((j : Fin r) → A (e.symm j)) k hk N
      ((i : ι) → X i) pt := by
    rw [hpt] at hhomeo
    exact hhomeo
  exact Work.RatHurewicz.isEMSpaceUpTo_of_addEquiv hk pt h2 (addEquivPiCongrLeft' A e).symm

end

end Work.EMFG
