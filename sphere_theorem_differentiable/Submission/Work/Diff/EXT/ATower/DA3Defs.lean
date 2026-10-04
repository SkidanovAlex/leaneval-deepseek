import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs
import Submission.Work.Diff.EXT.ConnCov.aOf_hasDerivAt
import Submission.Work.Diff.EXT.ConnCov.dtMet
import Submission.Work.Diff.EXT.ric_bound_of_curvBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the `dAOfBase` reaction bound

The reaction `Work.Diff.EXT.ConnCov.dAOfBase G t = ∂ₜ aOf(G ·)|ₜ` — the base of the tower of the
assignment `Diff/EXT/ATower/dAOfTowerBoundShi_piece` — is the following combination of the *fixed*
covariant derivative `∇^{G 0}Ric(G t)` of the Ricci tensor of `G t` (with the first value slot used
as the derivation direction):

`dAOfBase G t X Y Z x = -(ρ(X,Y,Z) + ρ(Y,X,Z) - ρ(Z,X,Y))`,   `ρ(U,V,W) = (∇^{G 0}_U Ric(G t))(V,W)`.

This module isolates the two objects involved:

* `rho3 G t` — the `(0,3)`-tensor `ρ = ∇^{G 0}Ric(G t)`, as an `Op3 0` (its `∇^{G 0}`-tower at
  level `k` is an index re-shuffling of the fixed Ricci tower `∇^{G 0,k+1}Ric`);
* `dR3 G t` — the Koszul combination above, again as an `Op3 0`;

together with the pointwise identity `dAOfBase G t = dR3 G t` on smooth fields
(`dAOfBase_eq_dR3`), which is how the reaction is handed to the tower machinery.  (The old
`rho3_apply` bridging to `ConnCov.S₀` moved to `DA3S₀.lean`, which carries the import of the
`ConnCov.dAOfTowerBoundShi*` family; this module is deliberately independent of that family.)

## Proof of the identity (self-contained)

`Work.Diff.EXT.ConnCov.aOf_hasDerivAt` (proved, in the stable module `ConnCov/aOf_hasDerivAt.lean`)
gives the derivative of `s ↦ aOf G s X Y Z x` as the *moving*-connection Koszul combination of
`dtMet G t = -2 Ric(G t)` plus the term `-2 Ric(∇^{Gt}_YX - ∇^{G0}_YX, Z x)`.  Then:

* `dtMet G t = -2 Ric` and `covDerivSym2` is linear in the lowered form
  (`covDerivSym2_const_mul_self`) turn the three moving Koszul terms into `-2` times the moving
  derivatives of `Ric`;
* `covDerivSym2_transfer_self` moves each moving derivative of `Ric` to the fixed connection at the
  cost of two `δ := covDiff G t`-insertions (`δ` is symmetric, `covDiff_symm_self`, because both
  connections are torsion free);
* the six `Ric(δ(·,·),·)`-terms cancel against the `-2 Ric(δ(Y,X), Z x)`-term, using the symmetry of
  `Ric` (`ricAt_symm_L`).

`ring` then closes the goal.

## Why

`tower (lcOf (G 0)) (dR3 G t) k` is the Koszul combination of the tower of the single tensor `rho3`,
and `tower (lcOf (G 0)) (rho3 G t) k` is (an index re-shuffling of) `tower2 (lcOf (G 0))
(baseRic2 (G t)) (k+1)` — the fixed `(0,2)`-Ricci tower at level `k + 1`.  Hence a uniform bound on
the latter (Shi's estimate plus the `∇^{G 0}`-tower bounds of the connection difference) yields the
requested bound on `tower (lcOf (G 0)) (dAOfBase G t) k`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The fixed (`∇^{G 0}`-)covariant derivative of the Ricci tensor of `G t`, as an `Op3 0`:
`rho3 G t _ X Y Z y = (∇^{G 0}_X Ric(G t))(Y,Z)(y)`.  (The first value slot is the derivation
direction, so this is a genuine `(0,3)`-tensor and its `∇^{G 0}`-tower is tensorial.) -/
noncomputable def rho3 (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) : Op3 (I := I) (M := M) 0 :=
  fun _ X Y Z y =>
    Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G 0))
      (fun (z : M) (a b : TangentSpace I z) =>
        Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z a b) X Y Z y

/-- The Koszul combination `-(ρ(X,Y,Z) + ρ(Y,X,Z) - ρ(Z,X,Y))` of `rho3`, as an `Op3 0`. -/
noncomputable def dR3 (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) : Op3 (I := I) (M := M) 0 :=
  fun _ X Y Z y =>
    -(rho3 G t (Fin.elim0 : Fin 0 → TF (I := I) (M := M)) X Y Z y
      + rho3 G t (Fin.elim0 : Fin 0 → TF (I := I) (M := M)) Y X Z y
      - rho3 G t (Fin.elim0 : Fin 0 → TF (I := I) (M := M)) Z X Y y)

/-- **`covDerivSym2` is linear in the lowered bilinear form.** -/
theorem covDerivSym2_const_mul_self
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (c : ℝ)
    (h : Π y : M, TangentSpace I y → TangentSpace I y → ℝ)
    (X Y Z : TF (I := I) (M := M)) (x : M) :
    Submission.Diff.covDerivSym2 cov (fun y a b => c * h y a b) X Y Z x
      = c * Submission.Diff.covDerivSym2 cov h X Y Z x := by
  have hfun : (fun y : M => c * h y (Y y) (Z y))
      = (fun y : M => c • (fun y' : M => h y' (Y y') (Z y')) y) := by
    funext y
    rw [smul_eq_mul]
  rw [Submission.Diff.covDerivSym2, Submission.Diff.covDerivSym2, hfun,
    Commons.Geometry.Manifold.Riemannian.mvfderiv_const_smul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Level-`1` transfer for `covDerivSym2`**: replacing the moving connection `∇^{G t}` by the
fixed one `∇^{G 0}` in the covariant derivative of a lowered bilinear form `h` (additive in each
slot) costs exactly the two `δ := covDiff G t`-insertions. -/
theorem covDerivSym2_transfer_self (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (h : Π y : M, TangentSpace I y → TangentSpace I y → ℝ)
    (hadd : ∀ (y : M) (a b c : TangentSpace I y),
      h y (a + b) c = h y a c + h y b c)
    (hadd₂ : ∀ (y : M) (a b c : TangentSpace I y),
      h y a (b + c) = h y a b + h y a c)
    (X Y Z : TF (I := I) (M := M)) (x : M) :
    Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) h X Y Z x
      = Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G 0)) h X Y Z x
        - h x (Work.Diff.EXT.ConnCov.covDiff G t Y X x) (Z x)
        - h x (Y x) (Work.Diff.EXT.ConnCov.covDiff G t Z X x) := by
  have e1 : Submission.Diff.lcOf (G t) Y x (X x)
      = Work.Diff.EXT.ConnCov.covDiff G t Y X x + Submission.Diff.lcOf (G 0) Y x (X x) :=
    sub_eq_iff_eq_add.mp rfl
  have e2 : Submission.Diff.lcOf (G t) Z x (X x)
      = Work.Diff.EXT.ConnCov.covDiff G t Z X x + Submission.Diff.lcOf (G 0) Z x (X x) :=
    sub_eq_iff_eq_add.mp rfl
  simp only [Submission.Diff.covDerivSym2, e1, e2]
  rw [hadd x (Work.Diff.EXT.ConnCov.covDiff G t Y X x) (Submission.Diff.lcOf (G 0) Y x (X x))
        (Z x),
    hadd₂ x (Y x) (Work.Diff.EXT.ConnCov.covDiff G t Z X x) (Submission.Diff.lcOf (G 0) Z x (X x))]
  ring

/-- **The connection difference of two torsion-free connections is symmetric.** -/
theorem covDiff_symm_self (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (X Y : TF (I := I) (M := M)) (hX : SmE I M X) (hY : SmE I M Y) (x : M) :
    Work.Diff.EXT.ConnCov.covDiff G t X Y x = Work.Diff.EXT.ConnCov.covDiff G t Y X x := by
  have hXd : MDiffAt (T% X) x := hX.mdifferentiableAt (by simp)
  have hYd : MDiffAt (T% Y) x := hY.mdifferentiableAt (by simp)
  have h1 := (Submission.Diff.lcOf (G t)).torsion_apply (X := X) (Y := Y) hXd hYd
  have h2 := (Submission.Diff.lcOf (G 0)).torsion_apply (X := X) (Y := Y) hXd hYd
  have ht1 : (Submission.Diff.lcOf (G t)).torsion x (X x) (Y x) = 0 := by
    have h : (Submission.Diff.lcOf (G t)).torsion = 0 := (hLC (G t)).2.1
    rw [h]; simp
  have ht0 : (Submission.Diff.lcOf (G 0)).torsion x (X x) (Y x) = 0 := by
    have h : (Submission.Diff.lcOf (G 0)).torsion = 0 := (hLC (G 0)).2.1
    rw [h]; simp
  rw [ht1] at h1
  rw [ht0] at h2
  have h1' : Submission.Diff.lcOf (G t) Y x (X x) - Submission.Diff.lcOf (G t) X x (Y x)
      = mlieBracket I X Y x := sub_eq_zero.mp h1.symm
  have h2' : Submission.Diff.lcOf (G 0) Y x (X x) - Submission.Diff.lcOf (G 0) X x (Y x)
      = mlieBracket I X Y x := sub_eq_zero.mp h2.symm
  have h1'' : Submission.Diff.lcOf (G t) Y x (X x)
      = mlieBracket I X Y x + Submission.Diff.lcOf (G t) X x (Y x) := by
    rw [← h1']; abel
  have h2'' : Submission.Diff.lcOf (G 0) Y x (X x)
      = mlieBracket I X Y x + Submission.Diff.lcOf (G 0) X x (Y x) := by
    rw [← h2']; abel
  simp only [Work.Diff.EXT.ConnCov.covDiff]
  rw [h1'', h2'']
  abel

/-- **The reaction is the Koszul combination of `∇^{G 0}Ric(G t)`**: the pointwise identity
`dAOfBase G t = dR3 G t` on smooth fields.  Derived from the proved
`Work.Diff.EXT.ConnCov.aOf_hasDerivAt` (the first variation of the lowered connection difference)
together with the transfer lemma and the torsion/symmetry lemmas above. -/
theorem dAOfBase_eq_dR3
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (X Y Z : TF (I := I) (M := M))
    (hX : SmE I M X) (hY : SmE I M Y) (hZ : SmE I M Z) (x : M) :
    Work.Diff.EXT.ConnCov.dAOfBase G t (Fin.elim0 : Fin 0 → TF (I := I) (M := M)) X Y Z x
      = dR3 G t (Fin.elim0 : Fin 0 → TF (I := I) (M := M)) X Y Z x := by
  have hcovt : CovariantDerivative.ContMDiffCovariantDerivative
      (Submission.Diff.lcOf (G t)) (⊤ : ℕ∞) := (hLC (G t)).1.some
  have hadd1 : ∀ (y : M) (a b c : TangentSpace I y),
      Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y (a + b) c
        = Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a c
          + Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y b c :=
    fun y a b c => Work.Diff.EXT.ricAt_add_middle_L (G t) hcovt y a b c
  have hadd2 : ∀ (y : M) (a b c : TangentSpace I y),
      Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a (b + c)
        = Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a b
          + Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a c :=
    fun y a b c => Work.Diff.EXT.ricAt_add_last_L (G t) hcovt y a b c
  have hderiv : deriv (fun s : ℝ => Work.Diff.EXT.aOf G s X Y Z x) t
      = -2 * Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x
            (Work.Diff.EXT.ConnCov.covDiff G t Y X x) (Z x)
          + (1 / 2 : ℝ) * (Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                (Submission.Diff.dtMet G t) X Y Z x
              + Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                (Submission.Diff.dtMet G t) Y X Z x
              - Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                (Submission.Diff.dtMet G t) Z X Y x) := by
    have h := (Work.Diff.EXT.ConnCov.aOf_hasDerivAt (I := I) (M := M) hLC
      (G := G) (T := T) hflow ht (X := X) (Y := Y) (Z := Z) hX hY hZ x).deriv
    simpa only [Work.Diff.EXT.ConnCov.covDiff] using h
  rw [show Work.Diff.EXT.ConnCov.dAOfBase G t (Fin.elim0 : Fin 0 → TF (I := I) (M := M))
        X Y Z x = deriv (fun s : ℝ => Work.Diff.EXT.aOf G s X Y Z x) t from rfl, hderiv]
  have hdtfun : Submission.Diff.dtMet G t
      = fun z p q => (-2 : ℝ) * Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q := by
    funext z p q
    exact Work.Diff.EXT.ConnCov.dtMet_eq_of_flow hflow ht z p q
  rw [hdtfun]
  rw [covDerivSym2_const_mul_self (Submission.Diff.lcOf (G t)) (-2)
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) X Y Z x,
      covDerivSym2_const_mul_self (Submission.Diff.lcOf (G t)) (-2)
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) Y X Z x,
      covDerivSym2_const_mul_self (Submission.Diff.lcOf (G t)) (-2)
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) Z X Y x]
  rw [covDerivSym2_transfer_self G t
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) hadd1 hadd2 X Y Z x,
      covDerivSym2_transfer_self G t
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) hadd1 hadd2 Y X Z x,
      covDerivSym2_transfer_self G t
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) hadd1 hadd2 Z X Y x]
  rw [covDiff_symm_self (I := I) (M := M) hLC G t Y X hY hX x,
      covDiff_symm_self (I := I) (M := M) hLC G t Z X hZ hX x,
      covDiff_symm_self (I := I) (M := M) hLC G t Z Y hZ hY x]
  rw [Work.Diff.EXT.ricAt_symm_L hLC (G t) hcovt x
        (Work.Diff.EXT.ConnCov.covDiff G t X Z x) (Y x)]
  simp only [Work.Diff.EXT.ConnCov.covDiff, dR3, rho3]
  ring

end Work.Diff.EXT.ATower
