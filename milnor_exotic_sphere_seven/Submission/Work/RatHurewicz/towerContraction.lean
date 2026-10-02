import Mathlib
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.CubicalDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chain contraction attached to a filling tower

For a filling family `K : Tower x₀ N` (Hutchings' `K`-operator, `fillingFamilyConst.lean`) the
faces of `K n p` are, by the tower axioms `hα` (top `p`, bottom the constant cube) and `hβ` (the
side faces are `K (n-1)` of the faces of `p`), so that

`∂ (K (n+1) c) = (-1)^{n+2} c + (-1)^{n+1} aug(c) · (constant (n+1)-cube) + K n (∂ c)`

for every `(n+1)`-chain `c`, where `aug` is the augmentation (sum of coefficients) and `K n` is
extended `ℤ`-linearly to chains.

In the **reduced** complex `C̄ = Cub / (constant cubes)` — which is legitimate because `hγ` says
that `K n` of the constant cube is the constant cube, so `K n` descends — this reads

`∂̄ ∘ K̄_n = (-1)^{n+1} id + K̄_{n-1} ∘ ∂̄`,

i.e. `K̄` is a **chain contraction**: the reduced cubical complex of `X` is acyclic in all degrees
`≤ N`.  Since a `Tower x₀ N` exists precisely when `π_i(X,x₀) = 0` for `i ≤ N`, this is the
chain-level form of "`X` has no reduced homology below degree `N+1`", and it is the cubical
counterpart of Hutchings' identity `∂K(σ) = σ - K(∂σ) - Φ(Ψ(σ))` (his `Φ` is zero in the reduced
complex).

The identity is used in `Submission/Work/RatHurewicz/psiKillsDegenerates.lean`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The `n`-th filling operator of a tower, extended `ℤ`-linearly to cubical `n`-chains. -/
def Klin {x₀ : X} {N : ℕ} (K : Tower x₀ N) (n : ℕ) : Cub n X →ₗ[ℤ] Cub (n + 1) X :=
  Finsupp.linearCombination ℤ fun s : C(IC n, X) => Finsupp.single (K.Kf n s) (1 : ℤ)

@[simp] theorem Klin_single {x₀ : X} {N : ℕ} (K : Tower x₀ N) (n : ℕ) (s : C(IC n, X)) :
    Klin K n (Finsupp.single s 1) = Finsupp.single (K.Kf n s) (1 : ℤ) := by
  rw [Klin, Finsupp.linearCombination_single, one_smul]

theorem Klin_single_smul {x₀ : X} {N : ℕ} (K : Tower x₀ N) (n : ℕ) (s : C(IC n, X))
    (a : ℤ) :
    Klin K n (Finsupp.single s a) = a • Finsupp.single (K.Kf n s) (1 : ℤ) := by
  rw [Klin, Finsupp.linearCombination_single]

/-- The augmentation of the cubical `n`-chains: the sum of the coefficients. -/
def aug (n : ℕ) : Cub n X →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun _ : C(IC n, X) => (1 : ℤ)

@[simp] theorem aug_single (n : ℕ) (s : C(IC n, X)) :
    aug (X := X) n (Finsupp.single s 1) = 1 := by
  rw [aug, Finsupp.linearCombination_single, one_smul]

theorem aug_smul_single (n : ℕ) (s : C(IC n, X)) (a : ℤ) :
    aug (X := X) n (Finsupp.single s a) = a := by
  rw [aug, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

/-- `cubD` of a `K`-filling, on a single cube: the tower axioms `hα`, `hβ` read off the faces. -/
theorem cubD_single_Kf {x₀ : X} {N : ℕ} (K : Tower x₀ N) (n : ℕ) (hn : n + 1 ≤ N)
    (p : C(IC (n + 1), X)) :
    cubD (n + 1) X (Finsupp.single (K.Kf (n + 1) p) (1 : ℤ)) =
      (-1 : ℤ) ^ (n + 1) • (Finsupp.single (cconst (n + 1) x₀) (1 : ℤ)
          - Finsupp.single p (1 : ℤ))
        + Klin K n (cubD n X (Finsupp.single p (1 : ℤ))) := by
  rw [cubD_single, Fin.sum_univ_castSucc]
  have hlast : (-1 : ℤ) ^ ((Fin.last (n + 1) : Fin (n + 1 + 1)) : ℕ) •
        (Finsupp.single (faceCube (Fin.last (n + 1)) 0 (K.Kf (n + 1) p)) (1 : ℤ)
          - Finsupp.single (faceCube (Fin.last (n + 1)) 1 (K.Kf (n + 1) p)) (1 : ℤ)) =
      (-1 : ℤ) ^ (n + 1) • (Finsupp.single (cconst (n + 1) x₀) (1 : ℤ)
          - Finsupp.single p (1 : ℤ)) := by
    rw [Fin.val_last]
    simp only [faceCube]
    rw [(K.hα (n + 1) hn p).2, (K.hα (n + 1) hn p).1]
  have hside : ∀ l : Fin (n + 1),
      (-1 : ℤ) ^ ((Fin.castSucc l : Fin (n + 1 + 1)) : ℕ) •
          (Finsupp.single (faceCube (Fin.castSucc l) 0 (K.Kf (n + 1) p)) (1 : ℤ)
            - Finsupp.single (faceCube (Fin.castSucc l) 1 (K.Kf (n + 1) p)) (1 : ℤ))
        = (-1 : ℤ) ^ (l : ℕ) • (Klin K n
            (Finsupp.single (faceCube l 0 p) (1 : ℤ)
              - Finsupp.single (faceCube l 1 p) (1 : ℤ))) := by
    intro l
    rw [Fin.val_castSucc]
    simp only [faceCube]
    rw [(K.hβ n hn p l).1, (K.hβ n hn p l).2, map_sub, Klin_single, Klin_single]
  rw [Finset.sum_congr rfl fun l _ => hside l, hlast]
  have hc : cubD n X (Finsupp.single p (1 : ℤ))
      = ∑ l : Fin (n + 1), (-1 : ℤ) ^ (l : ℕ) •
          (Finsupp.single (faceCube l 0 p) (1 : ℤ) - Finsupp.single (faceCube l 1 p) (1 : ℤ)) :=
    cubD_single p
  rw [hc, map_sum]
  simp only [map_smul]
  abel

/-- The **chain contraction** attached to a filling tower, in the form used downstream:
for every `(n+1)`-chain `c`,

`∂ (K (n+1) c) = (-1)^{n+1} (aug c · const - c) + K n (∂ c)`,

where `aug` is the augmentation (sum of the coefficients) and `K n` is extended `ℤ`-linearly. -/
theorem towerChainContraction {x₀ : X} {N : ℕ} (K : Tower x₀ N) (n : ℕ) (hn : n + 1 ≤ N)
    (c : Cub (n + 1) X) :
    cubD (n + 1) X (Klin K (n + 1) c) =
      (-1 : ℤ) ^ (n + 1) •
          (aug (X := X) (n + 1) c •
              Finsupp.single (cconst (n + 1) x₀) (1 : ℤ) - c)
        + Klin K n (cubD n X c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      rw [map_add (Klin K (n + 1)) f₁ f₂, map_add (cubD (n + 1) X) (Klin K (n + 1) f₁)
          (Klin K (n + 1) f₂), h₁, h₂, map_add (cubD n X) f₁ f₂,
        map_add (Klin K n) (cubD n X f₁) (cubD n X f₂),
        map_add (aug (X := X) (n + 1)) f₁ f₂]
      simp only [add_smul, smul_add, smul_sub, smul_smul, mul_add]
      abel
  | single p a =>
      have hsa : (Finsupp.single p a : Cub (n + 1) X) = a • Finsupp.single p (1 : ℤ) := by
        ext q
        by_cases h : q = p <;> simp [h, Finsupp.smul_apply]
      have hs : Klin K (n + 1) (Finsupp.single p a)
          = a • Klin K (n + 1) (Finsupp.single p (1 : ℤ)) := by
        rw [Klin_single, Klin_single_smul]
      rw [hs, map_smul (cubD (n + 1) X), Klin_single, cubD_single_Kf K n hn p,
        aug_smul_single, hsa, map_smul (cubD n X), map_smul (Klin K n)]
      simp only [smul_add, smul_sub]
      rw [smul_comm a ((-1 : ℤ) ^ (n + 1)) (Finsupp.single (cconst (n + 1) x₀) (1 : ℤ)),
        smul_comm a ((-1 : ℤ) ^ (n + 1)) (Finsupp.single p (1 : ℤ))]

/-- **`H̄`-acyclicity of the reduced cubical complex.**  Modulo the span of the constant cube at
`x₀`, the filling tower satisfies the chain-contraction identity
`∂̄ ∘ K̄ = (-1)^{n+1} id + K̄ ∘ ∂̄`.  Since a tower exists as soon as `π_i(X) = 0` for `i ≤ N`, this
is the chain-level form of "the reduced homology of `X` vanishes in degrees `≤ N`". -/
theorem cubD_Klin_sub_mem_const {x₀ : X} {N : ℕ} (K : Tower x₀ N) (n : ℕ) (hn : n + 1 ≤ N)
    (c : Cub (n + 1) X) :
    cubD (n + 1) X (Klin K (n + 1) c) + (-1 : ℤ) ^ (n + 1) • c
        - Klin K n (cubD n X c) ∈ ConstChain (n + 1) X x₀ := by
  have h : ((-1 : ℤ) ^ (n + 1) * aug (X := X) (n + 1) c) •
      Finsupp.single (cconst (n + 1) x₀) (1 : ℤ) ∈ ConstChain (n + 1) X x₀ :=
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  rw [show cubD (n + 1) X (Klin K (n + 1) c) + (-1 : ℤ) ^ (n + 1) • c
        - Klin K n (cubD n X c)
      = ((-1 : ℤ) ^ (n + 1) * aug (X := X) (n + 1) c) •
          Finsupp.single (cconst (n + 1) x₀) (1 : ℤ) from by
    rw [towerChainContraction K n hn c, smul_sub, smul_smul]
    abel]
  exact h

end

end Work.RatHurewicz
