import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linear algebra around `lieSub`

Shared vocabulary for `Work.BW.finrank_lieSub`.

The Lie algebra of `G = G_a × G_m^N` is `ℂ^{N+1}` (coordinate `0` is the `G_a` direction).
The subgroup `G' = G_a^ε × ker 𝒵` has Lie algebra `lieSub N ρ ε M` (see
`Submission/Work/BW/DefsMult.lean`). Writing `V = ℂ^{N+1}` and `U = ℂ^N`, the coordinate `0`
splits `V ≃ ℂ × U` as `v ↦ (v 0, lieTail v)`, with inverse `u ↦ lieCons u` for the zero
`G_a`-coordinate; the `ρ` characters have exponent matrix `M`, giving the linear map
`mLie M : U → ℂ^ρ`. Then

* `lieSub N ρ ε M = (if ε then ⊤ else ker (lieProj0 N)) ⊓ ker (mLie M ∘ lieTail N)`.

This file contains the definitions plus the elementary rewriting lemmas; the dimension
computations live in `Submission/Work/BW/finrank_lieSub.lean`.
-/

namespace Work.BW

noncomputable section

/-- The tail projection `ℂ^{N+1} → ℂ^N`, `v ↦ (v 1, …, v N)` (dropping the `G_a` coordinate). -/
def lieTail (N : ℕ) : (Fin (N + 1) → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun v := fun i => v i.succ
  map_add' x y := by funext i; rfl
  map_smul' a x := by funext i; rfl

/-- `ℂ^N → ℂ^{N+1}`, `u ↦ (0, u)`: the zero `G_a`-coordinate embedding. -/
def lieCons (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ) where
  toFun u := Fin.cons 0 u
  map_add' x y := by funext i; refine Fin.cases ?_ ?_ i <;> simp
  map_smul' a x := by funext i; refine Fin.cases ?_ ?_ i <;> simp

/-- The `G_a`-coordinate projection on `ℂ^{N+1}`. -/
abbrev lieProj0 (N : ℕ) : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) => ℂ) 0

/-- The exponent matrix `M`, cast entrywise to `ℂ`, as a linear map `ℂ^N → ℂ^ρ`
(so that the `j`-th character is `mLie M · j`). -/
def mLie {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) : (Fin N → ℂ) →ₗ[ℂ] (Fin ρ → ℂ) :=
  (Matrix.of (fun j i => ((M j i : ℂ)))).mulVecLin

@[simp] lemma lieTail_apply {N : ℕ} (v : Fin (N + 1) → ℂ) (i : Fin N) :
    lieTail N v i = v i.succ := rfl

@[simp] lemma lieTail_cons {N : ℕ} (a : ℂ) (u : Fin N → ℂ) :
    lieTail N (Fin.cons a u) = u := by funext i; rfl

@[simp] lemma lieTail_lieCons {N : ℕ} (u : Fin N → ℂ) :
    lieTail N (lieCons N u) = u := rfl

lemma lieCons_injective (N : ℕ) : Function.Injective (lieCons N) := by
  intro u v h
  have := congrArg (lieTail N) h
  simpa using this

/-- A vector with vanishing `G_a`-coordinate is the embedding of its own tail. -/
lemma lieCons_lieTail_of_apply_zero {N : ℕ} {v : Fin (N + 1) → ℂ} (hv : v 0 = 0) :
    lieCons N (lieTail N v) = v := by
  conv_rhs => rw [← Fin.cons_self_tail v]
  rw [hv]
  rfl

lemma lieTail_surjective (N : ℕ) : Function.Surjective (lieTail N : _ → (Fin N → ℂ)) :=
  fun u => ⟨lieCons N u, rfl⟩

lemma mLie_apply {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (u : Fin N → ℂ) (j : Fin ρ) :
    mLie M u j = ∑ i : Fin N, (M j i : ℂ) * u i := by
  simp [mLie, Matrix.mulVec_apply_eq_sum, Matrix.of_apply]

/-- The `ρ` character forms restricted to `ℂ^{N+1}` cut out the kernel of `mLie M ∘ lieTail`. -/
lemma iInf_ker_lieSub {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) :
    (⨅ j : Fin ρ, LinearMap.ker
        (∑ i : Fin N, ((M j i : ℂ)) •
          LinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) => ℂ) i.succ))
      = LinearMap.ker ((mLie M).comp (lieTail N)) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  have h : ∀ j : Fin ρ,
      ((∑ i : Fin N, ((M j i : ℂ)) •
          LinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) => ℂ) i.succ) v)
        = mLie M (lieTail N v) j := by
    intro j
    rw [mLie_apply]
    simp [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  constructor
  · intro hv
    funext j
    rw [← h j]
    exact hv j
  · intro hv j
    rw [h j]
    exact congrFun hv j

/-- `lieSub` in terms of the tail coordinates: the `ε`-part (`⊤`, or the hyperplane
`v 0 = 0`) intersected with the kernel of the characters. -/
lemma lieSub_eq_inf_ker_comp {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (ε : Bool) :
    lieSub N ρ ε M =
      (if ε then ⊤ else LinearMap.ker (lieProj0 N)) ⊓
        LinearMap.ker ((mLie M).comp (lieTail N)) := by
  simp only [lieSub, iInf_ker_lieSub M]

end

end Work.BW
