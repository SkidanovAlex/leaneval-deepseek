import Mathlib
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.MaxDom

/-!
# PERT · `Work.Pert.RBlock4.Rlow_holo`: holomorphy of the low return map `R_low`

`R_low` (`Work.Pert.Rlow`) is the low-height piece of the lifted return map of Shishikura
(4.2.2)/(A.4): at the point `w` it walks the level-`m` point `f^[m] (φ w)` of the orbit,
pulls it back through `τ` into the subgate `Qp'` (where `τ` is injective with nonvanishing
derivative), reads the upper Fatou coordinate `Φp` there, and undoes the iterate and the deck
shift.

Holomorphy is exactly the composition of three holomorphic maps, all of whose domain
requirements are supplied by the hypotheses:

* `w ↦ f^[m] (φ w)` is holomorphic on `U`: `φ` is, and each iterate of `f` is applied at a
  point of the *open* set `Df` on which `f` is holomorphic (`hwalk`);
* `y ↦ invOn τ Qp' y` is holomorphic on `τ '' Qp'`: the local inverse of `τ` at a point of the
  open set `Qp'`, where `deriv τ ≠ 0` and `τ` is injective (`MaxDom.seedP_holo` with `Φ := τ`
  and the outer map the identity);
* `Φp` is holomorphic on `Qp ⊇ Qp'`.

The subgate hypothesis `hland` says precisely that the walk lands in the image `τ '' Qp'`, so
the composition is defined everywhere on `U`.
-/

namespace Work.Pert.RBlock4

open Set

theorem Rlow_holo {f : ℂ → ℂ} {Df Qp Qp' U : Set ℂ} {τ Φp φ : ℂ → ℂ}
    {m : ℕ} {k : ℤ} {dlow : ℂ}
    (hU : IsOpen U) (hDf : IsOpen Df) (hf : DifferentiableOn ℂ f Df)
    (hQp : IsOpen Qp) (hQp' : IsOpen Qp') (hQp'sub : Qp' ⊆ Qp)
    (hτ : DifferentiableOn ℂ τ Qp) (hτne : ∀ z ∈ Qp', deriv τ z ≠ 0)
    (hinj : Set.InjOn τ Qp')
    (hΦp : DifferentiableOn ℂ Φp Qp)
    (hφ : DifferentiableOn ℂ φ U)
    (hwalk : ∀ w ∈ U, ∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df)
    (hland : ∀ w ∈ U, f^[m] (φ w) ∈ τ '' Qp') :
    DifferentiableOn ℂ (Work.Pert.Rlow f Qp' τ Φp φ m k dlow) U := by
  -- (1) `Φp ∘ invOn τ Qp'` is holomorphic on `τ '' Qp'` (local inverse + holomorphic outer map)
  have hseed : DifferentiableOn ℂ (seedP Φp τ Qp') (τ '' Qp') :=
    seedP_holo hQp' (hτ.mono hQp'sub) (hΦp.mono hQp'sub) hinj hτne
  -- (2) the walk `w ↦ f^[m] (φ w)` is holomorphic on `U`
  have hiter : ∀ n ≤ m, DifferentiableOn ℂ (fun w => f^[n] (φ w)) U := by
    intro n hn
    induction n with
    | zero => simpa using hφ
    | succ n ih =>
      have ih' : DifferentiableOn ℂ (fun w => f^[n] (φ w)) U :=
        ih (Nat.le_of_succ_le hn)
      have hmap : MapsTo (fun w => f^[n] (φ w)) U Df :=
        fun w hw => hwalk w hw n (Nat.le_of_succ_le hn)
      have hcomp2 := hf.comp ih' hmap
      have heq2 : (f ∘ fun w => f^[n] (φ w)) = fun w => f^[n+1] (φ w) := by
        funext w
        exact (Function.iterate_succ_apply' f n (φ w)).symm
      exact heq2 ▸ hcomp2
  have hF : DifferentiableOn ℂ (fun w => f^[m] (φ w)) U := hiter m le_rfl
  have hmapF : MapsTo (fun w => f^[m] (φ w)) U (τ '' Qp') := hland
  -- (3) compose, then subtract the constants `m`, `k` and add `dlow`
  have hmain : DifferentiableOn ℂ (fun w => seedP Φp τ Qp' (f^[m] (φ w))) U :=
    hseed.comp hF hmapF
  have heq : Work.Pert.Rlow f Qp' τ Φp φ m k dlow
      = fun w => seedP Φp τ Qp' (f^[m] (φ w)) - (m : ℂ) - (k : ℂ) + dlow := by
    funext w
    simp [Work.Pert.Rlow, seedP]
  rw [heq]
  exact ((hmain.sub (differentiableOn_const _)).sub (differentiableOn_const _)).add
    (differentiableOn_const _)

end Work.Pert.RBlock4
