import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# `exteriorPower.ιMulti` and determinants

If `w` is obtained from `u` by applying the matrix `A` (each new vector is a linear
combination of the `u i` with the coefficients taken from the corresponding column of
`A`), then the wedge products are related by the determinant:

`exteriorPower.ιMulti K k w = A.det • exteriorPower.ιMulti K k u`.

The proof goes through the general alternating-map statement
`alternatingMap_det_smul`: expand `ιMulti` at the linear combinations by multilinearity
(`MultilinearMap.map_sum` and `AlternatingMap.map_smul_univ`), keep only the terms
indexed by permutations (alternating maps vanish on non-injective families, and
injective self-maps of a finite type are permutations), and finally apply
`AlternatingMap.map_perm` to compare with the Leibniz formula for the determinant.
-/

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
together with the scalar-multiplication step in each coordinate. -/
private lemma alternatingMap_sum_functions {K : Type*} [Field K] {M : Type*}
    [AddCommGroup M] [Module K M] {N : Type*} [AddCommGroup N] [Module K N] {k : ℕ}
    (f : M [⋀^Fin k]→ₗ[K] N) (A : Matrix (Fin k) (Fin k) K) (u : Fin k → M) :
    f (fun j => ∑ i : Fin k, A i j • u i)
      = ∑ r : Fin k → Fin k, (∏ i : Fin k, A (r i) i) • f (u ∘ r) := by
  classical
  let F : MultilinearMap K (fun _ : Fin k => M) N := f.toMultilinearMap
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
private lemma alternatingMap_sum_perm {K : Type*} [Field K] {M : Type*}
    [AddCommGroup M] [Module K M] {N : Type*} [AddCommGroup N] [Module K N] {k : ℕ}
    (f : M [⋀^Fin k]→ₗ[K] N) (A : Matrix (Fin k) (Fin k) K) (u : Fin k → M) :
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
private lemma smul_sign_smul {K : Type*} [Field K] {N : Type*} [AddCommGroup N]
    [Module K N] (c : K) (s : ℤˣ) (x : N) :
    c • (s • x) = ((((s : ℤˣ) : ℤ) : K) * c) • x := by
  rw [Units.smul_def]
  have hcast : ((s : ℤ) : K) • x = (s : ℤ) • x := by
    exact Int.cast_smul_eq_zsmul (R := K) (n := (s : ℤ)) (b := x)
  rw [← hcast]
  rw [smul_smul]
  ring_nf

/-- The permutation sum occurring in the Leibniz formula for `A.det`, applied to an
arbitrary vector `x`, gives back `A.det • x`. -/
private lemma det_smul_final {K : Type*} [Field K] {N : Type*} [AddCommGroup N]
    [Module K N] {k : ℕ} (A : Matrix (Fin k) (Fin k) K) (x : N) :
    (∑ σ : Equiv.Perm (Fin k), (∏ i : Fin k, A (σ i) i) • (Equiv.Perm.sign σ • x))
      = A.det • x := by
  classical
  rw [Matrix.det_apply']
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact smul_sign_smul (K := K) (c := ∏ i : Fin k, A (σ i) i) (s := Equiv.Perm.sign σ) (x := x)

/-- Any alternating map, evaluated on vectors that are linear combinations of `u`
with coefficient matrix `A` (columns of `A` index the new vectors), is `A.det` times
its value at `u`. -/
private lemma alternatingMap_det_smul {K : Type*} [Field K] {M : Type*}
    [AddCommGroup M] [Module K M] {N : Type*} [AddCommGroup N] [Module K N] {k : ℕ}
    (f : M [⋀^Fin k]→ₗ[K] N) (A : Matrix (Fin k) (Fin k) K) (u : Fin k → M) :
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

/-- Applying a matrix to a family of vectors multiplies the exterior power (wedge
product) by the determinant of the matrix. -/
theorem iMulti_det_smul {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
    {k : ℕ} (u : Fin k → E) (A : Matrix (Fin k) (Fin k) K)
    (w : Fin k → E) (hw : ∀ j : Fin k,
      w j = (Finset.univ : Finset (Fin k)).sum (fun i : Fin k => A i j • u i)) :
    exteriorPower.ιMulti K k w = A.det • exteriorPower.ιMulti K k u := by
  classical
  calc
    exteriorPower.ιMulti K k w
        = exteriorPower.ιMulti K k (fun j : Fin k => ∑ i : Fin k, A i j • u i) := by
          congr 1
          exact funext hw
    _ = A.det • exteriorPower.ιMulti K k u := by
          exact alternatingMap_det_smul (f := exteriorPower.ιMulti K k) A u

end Commons.LinearAlgebra.ExteriorPower