import Mathlib
import Submission.Work.StemsB.rangeModelDefs
import Submission.Work.Serre.bijective_piMapN_of_joined
import Submission.Work.Serre.serrePostnikovTower

namespace Work.StemsB

open scoped Topology

/-!
# The two structure maps of the range-model tower are `π`-isomorphisms in range

`rmTower hm hZ t` is the level `t` of the CW model tower of `Z` built in
`Submission/Work/StemsB/rangeModelDefs.lean`: the states of the model tower of a `K(A, m+1)` are
run through the generator and killing steps, so that level `t` is a `StA Z z₀ (m - 1 + t)` whose
structure map `g` is a bijection on `π_i` for `i ≤ m + t`.

The lemma below is the final bookkeeping of that construction: at the last level `t = N - m`
(below degree `N`), *both* structure maps `g` and a second map `c : Y → P` into another range
model `P` of `K(A, m+1)` are `π`-isomorphisms in the range `≤ N`.

* For `g` this is the defining property of the tower (`StA.bij`), transferred to an arbitrary base
  point by path connectedness.
* For `c` the only information available is the invariant `SecondMapInv`: `c` matches `g` on base
  points, `π_{m+1}(c)` has the *same kernel* as the bijection `π_{m+1}(g)`, and `π_{m+1}(c)` is
  surjective.  Hence `π_{m+1}(c)` is an isomorphism at the base point (the equal-kernel condition
  with an injective map forces trivial kernel), and it propagates to every base point along paths.
* In all other degrees `i ≠ m+1` (`i ≤ N`) both `π_i(Y)` and `π_i(P)` are trivial — `Y` because
  `π_i(g)` is a bijection onto `π_i(Z) = 0`, and `P` because it is a range model — so any map
  between them is bijective.
-/

noncomputable section

/-- `Work.Serre.piMapN f (k+1)` is the underlying function of the monoid homomorphism
`Work.StemsB.πmap f k`; the two definitions are the same `Quotient.map`. -/
private lemma piMapN_eq_pimap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (k : ℕ) (x : X) :
    Work.Serre.piMapN f (k + 1) x = ⇑(πmap f k x) := rfl

/-- **A map with the kernel of an injective map is injective.**  If `f` induces an injection on
`π_{k+1}` and `h` has the same kernel as `f` at the base point, then `h` is injective there.
(The multiplicativity of `πmap` reduces the injectivity of `h` at `1` to the equality of kernels
and the factoriality of `πmap f`.) -/
private lemma injective_of_sameKernel {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {k : ℕ} (f : C(X, Y)) (h : C(X, Z)) (x : X)
    (hker : ∀ a : HomotopyGroup (Fin (k + 1)) X x,
      Work.Serre.piMapN f (k + 1) x a = 1 ↔ Work.Serre.piMapN h (k + 1) x a = 1)
    (hf : Function.Injective (Work.Serre.piMapN f (k + 1) x)) :
    Function.Injective (Work.Serre.piMapN h (k + 1) x) := by
  rw [piMapN_eq_pimap h k x] at hker ⊢
  rw [piMapN_eq_pimap f k x] at hker hf
  intro a b hab
  have h1 : πmap h k x (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : πmap f k x (a * b⁻¹) = 1 := (hker (a * b⁻¹)).mpr h1
  have h3 : πmap f k x (a * b⁻¹) = πmap f k x 1 := by rw [map_one]; exact h2
  exact mul_inv_eq_one.mp (hf h3)

theorem rmTower_pi_bijective {A : Type} [AddCommGroup A] {m N : ℕ} (hm : 1 ≤ m)
    {Z : Type} [TopologicalSpace Z] {z₀ : Z} {P : Type} [TopologicalSpace P] {p₀ : P}
    (hZ : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N Z z₀)
    (hP : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N P p₀) (hN : m + 1 ≤ N)
    (c : C((rmTower hm hZ (N - m)).Y, P))
    (hc : SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀) (rmTower hm hZ (N - m)).y₀
      (rmTower hm hZ (N - m)).g c) :
    (∀ i : ℕ, i ≤ N → ∀ y : (rmTower hm hZ (N - m)).Y,
        Function.Bijective (Work.Serre.piMapN (rmTower hm hZ (N - m)).g i y)) ∧
    (∀ i : ℕ, i ≤ N → ∀ y : (rmTower hm hZ (N - m)).Y,
        Function.Bijective (Work.Serre.piMapN c i y)) := by
  classical
  let s := rmTower hm hZ (N - m)
  haveI hconnY : PathConnectedSpace s.Y := s.conn
  haveI hconnZ : PathConnectedSpace Z := pathConnected_Z hm hZ
  haveI hconnP : PathConnectedSpace P := pathConnected_P hm hP
  -- the structure map of the tower is a `π_i`-isomorphism for `1 ≤ i ≤ N` at the tower's base point
  have hgp : ∀ i : ℕ, 1 ≤ i → i ≤ N → Function.Bijective (Work.Serre.piMapN s.g i s.y₀) := by
    intro i hi1 hiN
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact s.bij j (by omega)
  -- `π_i(Y)` is trivial in the degrees `i ≠ m+1`, `i ≤ N`
  have hgsub : ∀ i : ℕ, i ≠ m + 1 → (i < m + 1 ∨ i ≤ N) →
      Subsingleton (HomotopyGroup (Fin i) s.Y s.y₀) := by
    intro i hne hc'
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := s.Y) (x := s.y₀)).injective.subsingleton
    · have hZsub : Subsingleton (HomotopyGroup (Fin i) Z z₀) := hZ.2 i hne hc'
      have hZsub' : Subsingleton (HomotopyGroup (Fin i) Z (s.g s.y₀)) := by
        rw [s.gbase]; exact hZsub
      haveI := hZsub'
      exact (hgp i hpos (by omega)).injective.subsingleton
  -- the same at an arbitrary base point of `Y`
  have hgsub_any : ∀ i : ℕ, i ≠ m + 1 → (i < m + 1 ∨ i ≤ N) → ∀ y : s.Y,
      Subsingleton (HomotopyGroup (Fin i) s.Y y) := by
    intro i hne hc' y
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := s.Y) (x := y)).injective.subsingleton
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact Work.Serre.subsingleton_homotopyGroup_of_joined (PathConnectedSpace.joined s.y₀ y) j
        (hgsub (j + 1) hne hc')
  -- and `π_i(P)` is trivial in the same degrees, at every point of `P`
  have hPsub_any : ∀ i : ℕ, i ≠ m + 1 → (i < m + 1 ∨ i ≤ N) → ∀ p : P,
      Subsingleton (HomotopyGroup (Fin i) P p) := by
    intro i hne hc' p
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := P) (x := p)).injective.subsingleton
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact Work.Serre.subsingleton_homotopyGroup_of_joined (PathConnectedSpace.joined p₀ p) j
        (hP.2 (j + 1) hne hc')
  constructor
  · -- the first structure map
    intro i hi y
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have h1 : Subsingleton (HomotopyGroup (Fin 0) s.Y y) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := s.Y) (x := y)).injective.subsingleton
      have h2 : Subsingleton (HomotopyGroup (Fin 0) Z (s.g y)) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := Z) (x := s.g y)).injective.subsingleton
      exact ⟨fun a b _ => h1.elim a b, fun b => ⟨default, h2.elim _ _⟩⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact Work.Serre.bijective_piMapN_of_joined s.g (PathConnectedSpace.joined s.y₀ y) (j + 1)
        (hgp (j + 1) (by omega) (by omega))
  · -- the second structure map
    intro i hi y
    by_cases hcase : i = m + 1
    · -- the crucial degree: the equal-kernel condition and surjectivity make `π_{m+1}(c)` an iso
      subst hcase
      have hinj : Function.Injective (Work.Serre.piMapN c (m + 1) s.y₀) :=
        injective_of_sameKernel s.g c s.y₀ hc.2.1 (hgp (m + 1) (by omega) hN).injective
      exact Work.Serre.bijective_piMapN_of_joined c (PathConnectedSpace.joined s.y₀ y) (m + 1)
        ⟨hinj, hc.2.2⟩
    · -- all other degrees: both sides are trivial
      have hY := hgsub_any i hcase (Or.inr hi) y
      have hP' := hPsub_any i hcase (Or.inr hi) (c y)
      exact ⟨fun a b _ => hY.elim a b, fun b => ⟨default, hP'.elim _ _⟩⟩

end

end Work.StemsB
