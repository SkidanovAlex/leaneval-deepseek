import Mathlib
import Submission.Work.DSAMR.Defs
import Submission.Work.DSAMR.ECBase
import Submission.Work.DSAMR.ECHom

open CategoryTheory Limits

namespace Work.DSAMR

universe u

/-- **Almost null-homotopy of a chain map into an almost acyclic complex** (the K-projective / truncation argument; node **AMR** of the MIX2 design, `sources/dsmap/direct_summand_mix2.md`).

`K` is a cochain complex of `W`-modules indexed by `ℤ`, `e : W → K⁰` is a coaugmentation which is `I`-almost acyclic w.r.t. the tower `ϖ` (`Work.DSAMR.AlmostAcycZ`, i.e. the three conditions of the frozen `DSMap.Mix2.AlmostAcyc`): (1) `e w ∈ I·K⁰ ⟹ ϖ k * w ∈ I`; (2) every `z : K⁰` with `dz ∈ I·K¹` is `e w` modulo `I·K⁰` after multiplying by `ϖ k`; (3) every `z : K^(q+1)` with `dz ∈ I·K^(q+2)` is a coboundary modulo `I·K^(q+1)` after multiplying by `ϖ k`.

`P` is a bounded-above complex of finite free `A`-modules (so `P` is `K`-projective) and `ρ : P → K` is an `A`-linear chain map (`K` viewed as an `A`-complex through `ψ`).  Then there is a loss `L` (bounded by the number of degrees of `P`) such that for every level `j` there is an `A`-linear `h : P⁰ → W` with `ϖ j ^ L • ρ⁰ x ≡ e (h x)` modulo `I · K⁰` for every cocycle `x` of `P⁰`.

Proof plan (descending induction on the degree bound `N` with `Pⁱ = 0` for `i > N`; `L = N + 1` works).  For `q = N, N-1, …, 1` choose an `A`-linear `hᵠ : Pᵠ → K^(q-1)` whose values on a basis of the free module `Pᵠ` are provided by clause (3) of `AlmostAcycZ` applied to `R_q (b) := ϖ j ^ m • ρᵠ b - h^{q+1} (dᵠ b)`; the hypothesis `d (R_q b) ∈ I · K^{q+1}` needed to apply it is the *previous* relation, via `d ∘ ρ = ρ ∘ d` and `d ∘ d = 0`.  At `q = 0` use clause (2) of `AlmostAcycZ` with `R₀ := ϖ j ^ m • ρ⁰ - h¹ ∘ d⁰` to get `h⁰ : P⁰ → W`.  The accumulated factor `ϖ j` (one per degree) gives `L = N + 1`; on the cocycles of `P⁰` the `h¹ ∘ d⁰` term drops out.

Hints.  Extract the vanishing bound with `hP.2` and each degreewise freeness with `hP.1.1`, use
`Module.Free.chooseBasis` to build the `hᵠ` on a basis and extend `A`-linearly (the `A`-module
structure on `K.X i` is the one from `ModuleCat.restrictScalars ψ`, so `a • x = ψ a • x`).
The chain-map condition is `HomologicalComplex.Hom.comm'` (for `i j : ℤ` with `j = i + 1`), whose
element form is `ρ^{i+1} (d^i x) = d^i (ρ^i x)`. -/
theorem exists_coaug_lift {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W)
    (ϖ : ℕ → W) (I : Ideal W)
    {K : CochainComplex (ModuleCat.{u} W) ℤ} (e : ModuleCat.of W W ⟶ K.X 0)
    (hK : Work.DSAMR.AlmostAcycZ ϖ I K e)
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : DSMap.Mix.IsBddFinFree P)
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) :
    ∃ L : ℕ, ∀ j : ℕ,
      ∃ h : P.X 0 ⟶ (ModuleCat.restrictScalars ψ).obj (ModuleCat.of W W),
      ∀ x : P.X 0, (P.d 0 1).hom x = 0 →
        ϖ j ^ L • (show K.X 0 from (ρ.f 0) x) -
            e.hom (show W from h x) ∈ I • (⊤ : Submodule W (K.X 0)) := by
  classical
  -- write `N` for the vanishing bound of `P`, so that `P ^ i = 0` for `i > N`
  obtain ⟨N₀, hN₀⟩ := hP.2
  have hN : ∀ i : ℤ, ((N₀.toNat : ℕ) : ℤ) < i → IsZero (P.X i) :=
    fun i hi => hN₀ i (by omega)
  refine ⟨N₀.toNat + 1, fun t => ?_⟩
  -- the base case: level `N₀.toNat`, loss `t ^ 0 = 1`
  have hbase : ∃ h : P.X (((N₀.toNat : ℕ) : ℤ) + 1) ⟶
      (ModuleCat.restrictScalars ψ).obj (K.X (((N₀.toNat : ℕ) : ℤ))),
      ∀ y : P.X (((N₀.toNat : ℕ) : ℤ) + 1),
        (P.d (((N₀.toNat : ℕ) : ℤ) + 1) (((N₀.toNat : ℕ) : ℤ) + 1 + 1)).hom y = 0 →
        ϖ t ^ 0 • (show K.X (((N₀.toNat : ℕ) : ℤ) + 1) from
            (ρ.f (((N₀.toNat : ℕ) : ℤ) + 1)) y) -
          (K.d (((N₀.toNat : ℕ) : ℤ)) (((N₀.toNat : ℕ) : ℤ) + 1)).hom
            (show K.X (((N₀.toNat : ℕ) : ℤ)) from h y)
          ∈ I • (⊤ : Submodule W (K.X (((N₀.toNat : ℕ) : ℤ) + 1))) := by
    refine ⟨0, fun y _ => ?_⟩
    exact rel_of_subsingleton ψ ϖ ρ I
      (ModuleCat.subsingleton_of_isZero (M := P.X (((N₀.toNat : ℕ) : ℤ) + 1)) (hN _ (by omega)))
      0 t 0 y
  -- the descending induction: `hmain m j` gives the level-`(j:ℤ)` datum with loss `t ^ m`,
  -- where `j + m = N₀.toNat`
  have hmain : ∀ m : ℕ, ∀ j : ℕ, j + m = N₀.toNat →
      ∃ h : P.X ((j:ℤ)+1) ⟶ (ModuleCat.restrictScalars ψ).obj (K.X (j:ℤ)),
      ∀ y : P.X ((j:ℤ)+1), (P.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom y = 0 →
        ϖ t ^ m • (show K.X ((j:ℤ)+1) from (ρ.f ((j:ℤ)+1)) y) -
          (K.d (j:ℤ) ((j:ℤ)+1)).hom (show K.X (j:ℤ) from h y)
            ∈ I • (⊤ : Submodule W (K.X ((j:ℤ)+1))) := by
    intro m
    induction m with
    | zero =>
      intro j hj
      subst hj
      exact hbase
    | succ m ih =>
      intro j hj
      have hj' : (j + 1) + m = N₀.toNat := by omega
      exact ec_step_proved ψ ϖ I e hK hP ρ t j m (ih (j + 1) hj')
  obtain ⟨h1, hrel1⟩ := hmain N₀.toNat 0 (by omega)
  -- the degree-`0` endgame, with total loss `t ^ (N₀.toNat + 1)`
  exact ec_final_proved ψ ϖ I e hK hP ρ t N₀.toNat h1 hrel1

end Work.DSAMR
