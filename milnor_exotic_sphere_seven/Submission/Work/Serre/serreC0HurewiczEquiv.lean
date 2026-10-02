import Mathlib
import Submission.Work.Stems.HurewiczFirstDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Hurewicz isomorphism in the first non-vanishing degree, packaged as a group isomorphism

This is the packaging step used by the subproject SERRE: the integral Hurewicz theorem
(`Work.Stems.hurewicz_first_degree`) gives a *bijection* `π_m(X,x₀) → H_m(X;ℤ)` when `X` is
`(m-1)`-connected, and the additivity of the Hurewicz map (`Work.Stems.hurewiczMapN_mul`) upgrades
it to a *group* isomorphism.  Composing with any `ℤ`-linear identification `H_m(X;ℤ) ≃ A` produces
a multiplicative equivalence `π_m(X,x₀) ≃* Multiplicative A` — the form in which the models
`K(A,m)` are consumed (`Work.Serre.IsEMSpace`).

The statement is in the `multiplicative` convention of Mathlib's `HomotopyGroup (Fin m) X x₀ = π_m`,
so the additive group `A` is wrapped in `Multiplicative`.

Nothing here needs the group structure on `HomotopyGroup (Fin m)` beyond Mathlib's instance (which
is available as soon as `Fin m` is nonempty), and the additivity of the Hurewicz map is applied in
the shifted form `m = k + 1` in which it is stated.
-/

namespace Work.Serre

theorem serreC0HurewiczEquiv {X : Type} [TopologicalSpace X] {m : ℕ} (hm : 2 ≤ m) (x₀ : X)
    (hconn : ∀ j, j < m → Subsingleton (HomotopyGroup (Fin j) X x₀))
    {A : Type} [AddCommGroup A]
    (e : ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology m) ≃ₗ[ℤ] A) :
    letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    Nonempty (HomotopyGroup (Fin m) X x₀ ≃* Multiplicative A) := by
  -- the target is `π_{k+1}`, the shape in which the additivity of the Hurewicz map is stated
  rcases m with _ | k
  · omega
  · have hle : 1 ≤ Nat.succ k := Nat.succ_le_succ (Nat.zero_le k)
    -- Hurewicz: `π_{k+1}(X,x₀) → H_{k+1}(X;ℤ)` is a bijection
    have hbij : Function.Bijective (Work.Stems.hurewiczMapN (Nat.succ k) hle x₀) :=
      Work.Stems.hurewicz_first_degree (Nat.succ k) hm x₀ hconn
    -- additivity of the Hurewicz map
    have hmul : ∀ a b : HomotopyGroup (Fin (Nat.succ k)) X x₀,
        Work.Stems.hurewiczMapN (Nat.succ k) hle x₀ (a * b) =
          Work.Stems.hurewiczMapN (Nat.succ k) hle x₀ a +
            Work.Stems.hurewiczMapN (Nat.succ k) hle x₀ b :=
      fun a b => Work.Stems.hurewiczMapN_mul k x₀ a b
    have hf : Function.Bijective
        (fun g => Multiplicative.ofAdd (e (Work.Stems.hurewiczMapN (Nat.succ k) hle x₀ g))) :=
      (Multiplicative.ofAdd.bijective).comp (e.bijective.comp hbij)
    let F : HomotopyGroup (Fin (Nat.succ k)) X x₀ →ₙ* Multiplicative A :=
      { toFun := fun g =>
          Multiplicative.ofAdd (e (Work.Stems.hurewiczMapN (Nat.succ k) hle x₀ g))
        map_mul' := by
          intro a b
          rw [hmul a b, map_add]
          rfl }
    exact ⟨MulEquiv.ofBijective F hf⟩

end Work.Serre
