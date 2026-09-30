import Mathlib
import Submission.Work.Stems.Hur2b.cubD_comp_cubD
import Submission.Work.Stems.Hur2c.PsiLinGenCubD
import Submission.Work.RatHurewicz.cubicalBridgeDeg
import Submission.Work.Stems.Hur2c.hurewiczMapN_two_injective
import Submission.Work.Stems.HurewiczNeutral

/-!
# Injectivity of the Hurewicz map in degree `m + 2`, from the "degenerate cycles" input

This is the general-degree form of `Work.Stems.hurewiczMapN_two_injective`.  The degree-`2`
argument in `Submission/Work/Stems/Hur2c/` uses exactly four structural inputs:

* **(Z)** `psiLinGen_single_based`: `ΨLin (single p.1 1) = ⟦p⟧` for a *based* cube `p`;
* **(Y)** `psiLinGen_cubD_eq_zero`: `ΨLin (∂ c) = 0` for every `(m+3)`-chain `c`;
* **(E)** the vanishing of `ΨLin` on degenerate `(m+2)`-**cycles** — this is precisely the
  hypothesis `hdegen` below (Hutchings' footnote; see `PSI_DEG_NOTES.md` for why the naive
  "`Ψ` kills every degenerate cube" is not provable in this workspace);
* the chain-level bridge `Work.RatHurewicz.cubicalBridgeDeg`: a based `(m+2)`-cube with vanishing
  Hurewicz image is a boundary modulo the degenerate cubes.

Given these, the injectivity in degree `m + 2` is the same three-line computation as in degree `2`:
the bridge produces a chain `c` with `∂c ∓ single p.1 1` degenerate; the difference is a degenerate
cycle (a based cube has vanishing boundary), so `(E)` kills it; expanding `ΨLin` and using
`(Z)` and `(Y)` gives `⟦p⟧ = 1`.

The two elementary facts about based cubes needed here are recorded below in all dimensions.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.Hur2c

/-- A face of a *based* `(n+1)`-cube is the constant cube at the base point. -/
theorem faceCube_based_const_gen {X : Type} [TopologicalSpace X] {n : ℕ} (x₀ : X)
    (p : GenLoop (Fin (n + 1)) X x₀) (i : Fin (n + 1)) (b : unitInterval)
    (hb : b = 0 ∨ b = 1) :
    faceCube i b p.1 = ContinuousMap.const (IC n) x₀ := by
  ext t
  refine p.2 (faceCM i b t) ?_
  rw [Cube.boundary]
  rcases hb with rfl | rfl
  · exact ⟨i, Or.inl (Work.Stems.Hur2c.faceCM_frozen i 0 t)⟩
  · exact ⟨i, Or.inr (Work.Stems.Hur2c.faceCM_frozen i 1 t)⟩

/-- **A based `(n+1)`-cube is a cycle** in the cubical chain complex. -/
theorem cubD_single_based_gen {X : Type} [TopologicalSpace X] {n : ℕ} (x₀ : X)
    (p : GenLoop (Fin (n + 1)) X x₀) :
    cubD n X (Finsupp.single p.1 (1 : ℤ)) = 0 := by
  rw [cubD_single]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [faceCube_based_const_gen x₀ p i 0 (Or.inl rfl),
    faceCube_based_const_gen x₀ p i 1 (Or.inr rfl)]
  simp

/-- `∂ ∘ ∂ = 0`, in the form used here (no simple-connectivity hypothesis, unlike
`Work.Stems.cubD_comp_cubD_apply`). -/
theorem cubD_comp_cubD_apply_gen {X : Type} [TopologicalSpace X] (n : ℕ)
    (c : Cub (n + 2) X) :
    cubD n X (cubD (n + 1) X c) = 0 := by
  have h := congrArg (fun (f : Cub (n + 2) X →ₗ[ℤ] Cub n X) => f c)
    (Work.Stems.Hur2b.cubD_comp_cubD n (X := X))
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

/-- **Injectivity of the degree-`(m+2)` Hurewicz map**, from the degenerate-cycle input `hdegen`.

If `hdegen` says that the linearised filling `ΨLin` vanishes on every degenerate `(m+2)`-cycle,
then a based `(m+2)`-cube `p` whose Hurewicz image is zero is itself trivial in `π_{m+2}`. -/
theorem hurewiczMapN_injective_of_degen_cycle (N m : ℕ) [Nontrivial (Fin (m + 2))] {X : Type}
    [TopologicalSpace X] {x₀ : X}
    (K : Work.RatHurewicz.Tower x₀ N) (hN : m + 1 ≤ N)
    (hdegen : ∀ d : Work.Stems.Cubical.Cub (m + 2) X, d ∈ Work.RatHurewicz.Deg (m + 2) X →
      Work.Stems.Cubical.cubD (m + 1) X d = 0 → Work.Stems.Hur2c.psiLinGen N m K hN d = 0)
    (p : GenLoop (Fin (m + 2)) X x₀)
    (hp : Work.Stems.hurewiczMapN (m + 2) (by omega) x₀ (Quotient.mk _ p) = 0) :
    (Quotient.mk _ p : HomotopyGroup (Fin (m + 2)) X x₀) = ⟦GenLoop.const⟧ := by
  obtain ⟨c, hc | hc⟩ := Work.RatHurewicz.cubicalBridgeDeg (m + 2) (by omega) x₀ p hp
  · -- `∂c - single p.1 1 ∈ Deg (m+2) X`
    have hcomp : cubD (m + 1) X (cubD (m + 2) X c) = 0 :=
      cubD_comp_cubD_apply_gen (m + 1) c
    have hbased : cubD (m + 1) X (Finsupp.single p.1 (1 : ℤ)) = 0 :=
      cubD_single_based_gen x₀ p
    have hcyc : cubD (m + 1) X (cubD (m + 2) X c - Finsupp.single p.1 (1 : ℤ)) = 0 := by
      rw [map_sub, hcomp, hbased, sub_zero]
    have hpsi : psiLinGen N m K hN (Finsupp.single p.1 (1 : ℤ)) = 0 := by
      have h0 := hdegen (cubD (m + 2) X c - Finsupp.single p.1 (1 : ℤ)) hc hcyc
      rw [map_sub, psiLinGen_cubD_eq_zero N m K hN c, zero_sub, neg_eq_zero] at h0
      exact h0
    have hx := (psiLinGen_single_based N m K hN p).symm.trans hpsi
    have h1 := congrArg (fun z => Additive.toMul z) hx
    exact h1.trans HomotopyGroup.one_def
  · -- `∂c + single p.1 1 ∈ Deg (m+2) X`
    have hcomp : cubD (m + 1) X (cubD (m + 2) X c) = 0 :=
      cubD_comp_cubD_apply_gen (m + 1) c
    have hbased : cubD (m + 1) X (Finsupp.single p.1 (1 : ℤ)) = 0 :=
      cubD_single_based_gen x₀ p
    have hcyc : cubD (m + 1) X (cubD (m + 2) X c + Finsupp.single p.1 (1 : ℤ)) = 0 := by
      rw [map_add, hcomp, hbased, zero_add]
    have hpsi : psiLinGen N m K hN (Finsupp.single p.1 (1 : ℤ)) = 0 := by
      have h0 := hdegen (cubD (m + 2) X c + Finsupp.single p.1 (1 : ℤ)) hc hcyc
      rw [map_add, psiLinGen_cubD_eq_zero N m K hN c, zero_add] at h0
      exact h0
    have hx := (psiLinGen_single_based N m K hN p).symm.trans hpsi
    have h1 := congrArg (fun z => Additive.toMul z) hx
    exact h1.trans HomotopyGroup.one_def

end Work.Stems.Hur2c
