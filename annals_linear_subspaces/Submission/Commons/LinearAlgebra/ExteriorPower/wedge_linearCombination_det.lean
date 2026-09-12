import Mathlib.LinearAlgebra.ExteriorPower.Basic

open scoped BigOperators

namespace Commons.LinearAlgebra.ExteriorPower

/-- A sum over a finite type is the same as the sum over the subtype of elements
satisfying a predicate, provided the remaining summands vanish. -/
private lemma sum_univ_eq_sum_subtype {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] {M : Type*} [AddCommMonoid M] (F : α → M)
    (h : ∀ a, ¬ p a → F a = 0) :
    (∑ a : α, F a) = ∑ a : {a // p a}, F a.1 := by
  classical
  calc
    (∑ a : α, F a) = ∑ a : α, if p a then F a else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      by_cases hp : p a
      · simp [hp]
      · simp [hp, h a hp]
    _ = ∑ a ∈ Finset.univ.filter p, F a := by
      rw [Finset.sum_filter]
    _ = ∑ a : {a // p a}, F a.1 := by
      exact Finset.sum_subtype (s := Finset.univ.filter p) (h := by intro x; simp) F

/-- Multilinear expansion of an alternating map at a family of linear combinations,
together with the scalar-multiplication step in each coordinate.  Here `w` is
indexed by the columns of `A` (`w j = ∑ i, A i j • u i`), matching the
`det_apply'` convention. -/
private lemma alternatingMap_sum_functions {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] {k : ℕ}
    (f : M [⋀^Fin k]→ₗ[R] N) (A : Matrix (Fin k) (Fin k) R) (u : Fin k → M) :
    f (fun j => ∑ i : Fin k, A i j • u i)
      = ∑ r : Fin k → Fin k, (∏ i : Fin k, A (r i) i) • f (u ∘ r) := by
  classical
  let F : MultilinearMap R (fun _ : Fin k => M) N := f.toMultilinearMap
  have h := MultilinearMap.map_sum (f := F) (α := fun _ : Fin k => Fin k)
    (g := fun j i : Fin k => A i j • u i)
  calc
    f (fun j => ∑ i : Fin k, A i j • u i)
        = ∑ r : Fin k → Fin k, f (fun i : Fin k => A (r i) i • u (r i)) := by
            simpa [F] using h
    _ = ∑ r : Fin k → Fin k, (∏ i : Fin k, A (r i) i) • f (u ∘ r) := by
            apply Finset.sum_congr rfl
            intro r hr
            simpa using AlternatingMap.map_smul_univ (f := f) (c := fun i : Fin k => A (r i) i)
              (m := u ∘ r)

/-- In the expansion of an alternating map, the terms indexed by non-injective
functions vanish, so only the permutations remain. -/
private lemma alternatingMap_sum_perm {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] {k : ℕ}
    (f : M [⋀^Fin k]→ₗ[R] N) (A : Matrix (Fin k) (Fin k) R) (u : Fin k → M) :
    (∑ r : Fin k → Fin k, (∏ i : Fin k, A (r i) i) • f (u ∘ r))
      = ∑ σ : Equiv.Perm (Fin k), (∏ i : Fin k, A (σ i) i) • f (u ∘ σ) := by
  classical
  let p : (Fin k → Fin k) → Prop := fun r => Function.Injective r
  have hbijr : ∀ (r : Fin k → Fin k) (hr : p r), Function.Bijective r := by
    intro r hr
    exact (Fintype.bijective_iff_injective_and_card r).2 ⟨hr, rfl⟩
  let S : Type := {r : Fin k → Fin k // p r}
  let F : S → N := fun r => (∏ i : Fin k, A (r.1 i) i) • f (u ∘ r.1)
  let G : Equiv.Perm (Fin k) → N := fun σ => (∏ i : Fin k, A (σ i) i) • f (u ∘ σ)
  have hdrop :
    (∑ r : Fin k → Fin k, (∏ i : Fin k, A (r i) i) • f (u ∘ r)) = ∑ r : S, F r := by
      dsimp [F]
      exact sum_univ_eq_sum_subtype (α := Fin k → Fin k) (p := p)
        (F := fun r => (∏ i : Fin k, A (r i) i) • f (u ∘ r))
        (h := fun r hnr => by
           have hz : f (u ∘ r) = 0 :=
             AlternatingMap.map_eq_zero_of_not_injective f (u ∘ r)
                (by exact fun huj => hnr (Function.Injective.of_comp (f := u) huj))
           simp [hz])
  let efun : S → Equiv.Perm (Fin k) := fun x => Equiv.ofBijective x.1 (hbijr x.1 x.2)
  have he_inj : Function.Injective efun := by
    intro x y hxy
    apply Subtype.ext
    apply funext
    intro i
    have hto := congrArg Equiv.toFun hxy
    exact congr_fun hto i
  have he_surj : Function.Surjective efun := by
    intro σ
    refine ⟨⟨σ.1, Equiv.injective σ⟩, ?_⟩
    ext i
    simp [efun]
  let e : S ≃ Equiv.Perm (Fin k) := Equiv.ofBijective efun ⟨he_inj, he_surj⟩
  calc
    (∑ r : Fin k → Fin k, (∏ i : Fin k, A (r i) i) • f (u ∘ r)) = ∑ r : S, F r := hdrop
    _ = ∑ σ : Equiv.Perm (Fin k), G σ := by
      calc
        (∑ r : S, F r) = ∑ r : S, G (e r) := by
          apply Finset.sum_congr rfl
          intro r hr
          dsimp [F, G]
          have hcoe : (⇑(e r) : Fin k → Fin k) = r.1 := by
            apply funext
            intro i
            dsimp [e, efun]
            rfl
          simp [hcoe]
        _ = ∑ σ : Equiv.Perm (Fin k), G σ := by
          exact Equiv.sum_comp e G

/-- Multiplication by a scalar and by the sign of a permutation combine into the
product of the corresponding scalars. -/
private lemma smul_sign_smul {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N]
    [Module R N] (c : R) (s : ℤˣ) (x : N) :
    c • (s • x) = ((((s : ℤˣ) : ℤ) : R) * c) • x := by
  rw [Units.smul_def]
  have hcast : ((s : ℤ) : R) • x = (s : ℤ) • x := by
    exact Int.cast_smul_eq_zsmul (R := R) (n := (s : ℤ)) (b := x)
  rw [← hcast]
  rw [smul_smul]
  ring_nf

/-- The permutation sum occurring in the Leibniz formula for `A.det`, applied to an
arbitrary vector `x`, gives back `A.det • x`. -/
private lemma det_smul_final {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N]
    [Module R N] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) (x : N) :
    (∑ σ : Equiv.Perm (Fin k), (∏ i : Fin k, A (σ i) i) • (Equiv.Perm.sign σ • x))
      = A.det • x := by
  classical
  rw [Matrix.det_apply']
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact smul_sign_smul (R := R) (c := ∏ i : Fin k, A (σ i) i) (s := Equiv.Perm.sign σ) (x := x)

/-- Any alternating map, evaluated on vectors `w j = ∑ i, A i j • u i` that are linear
combinations of `u` with coefficient matrix `A` (columns of `A` index the new
vectors), is `A.det` times its value at `u`. -/
private lemma alternatingMap_det_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] {k : ℕ}
    (f : M [⋀^Fin k]→ₗ[R] N) (A : Matrix (Fin k) (Fin k) R) (u : Fin k → M) :
    f (fun j => ∑ i : Fin k, A i j • u i) = A.det • f u := by
  classical
  calc
    f (fun j => ∑ i : Fin k, A i j • u i)
        = ∑ r : Fin k → Fin k, (∏ i : Fin k, A (r i) i) • f (u ∘ r) :=
          alternatingMap_sum_functions f A u
    _ = ∑ σ : Equiv.Perm (Fin k), (∏ i : Fin k, A (σ i) i) • f (u ∘ σ) :=
          alternatingMap_sum_perm f A u
    _ = ∑ σ : Equiv.Perm (Fin k), (∏ i : Fin k, A (σ i) i) • (Equiv.Perm.sign σ • f u) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [AlternatingMap.map_perm (g := f) (v := u) σ]
    _ = A.det • f u := det_smul_final A (f u)

/--
The top wedge of linear combinations transforms by the determinant:
`∧ᵢ (Σⱼ aᵢⱼ • vⱼ) = det(a) • ∧ⱼ vⱼ` in the `n`-th exterior power of a module.

Used for the change-of-basis relation of covolumes of full-rank sublattices of a
common real span (H3 / intrinsic index identity): with `wᵢ = Σⱼ aᵢⱼ mⱼ` the two
wedge vectors satisfy `∧w = det(a) • ∧m`, so `‖∧w‖ = |det a|·‖∧m‖`.

Route hints (expand via multilinearity + alternation): show the alternating `n`-linear
map `(v₁,…,vₙ) ↦ ιMulti (fun i ↦ Σⱼ aᵢⱼ • vⱼ) − det(a) • ιMulti v` vanishes — expand the
left wedge over the functions `Fin n → Fin n`; non-injective multi-indices contribute 0
(alternating, repeated argument), permutations `σ` contribute `sign σ · (∏ᵢ aᵢ,σ(i)) ·
(v_{σ(1)}∧…∧v_{σ(n)}) = sign σ · (∏ᵢ aᵢσ(i)) · sign σ · (v₁∧…∧vₙ)`, and compare with
`Matrix.det_apply` (`det a = Σ_σ sign σ · ∏ᵢ aᵢ,σ(i)`).  The engine lemmas: the
alternating/multilinear properties of `exteriorPower.ιMulti` (e.g.
`AlternatingMap.map_sum`-type facts, `ιMulti` permutation/swap lemmas, scalar
multiplication in the exterior power).  No independence/finite-dimensionality of `M` is
needed — the identity holds in the tensor exterior power of any module.
-/
theorem wedge_linearCombination_det {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {n : ℕ} (v : Fin n → M) (a : Matrix (Fin n) (Fin n) R) :
    exteriorPower.ιMulti R n (fun i : Fin n => ∑ j : Fin n, a i j • v j) =
      a.det • exteriorPower.ιMulti R n v := by
  classical
  have hmain := alternatingMap_det_smul (R := R) (f := exteriorPower.ιMulti R n)
      (A := a.transpose) (u := v)
  -- hmain : ιMulti (fun j => ∑ i, aᵀ i j • v i) = aᵀ.det • ιMulti v
  calc
    exteriorPower.ιMulti R n (fun i : Fin n => ∑ j : Fin n, a i j • v j)
        = exteriorPower.ιMulti R n (fun j : Fin n => ∑ i : Fin n, a.transpose i j • v i) := by
          rfl
    _ = (a.transpose).det • exteriorPower.ιMulti R n v := hmain
    _ = a.det • exteriorPower.ιMulti R n v := by
          rw [Matrix.det_transpose]

end Commons.LinearAlgebra.ExteriorPower
