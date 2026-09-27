/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The Eilenberg–Zilber shuffle lemma for chains

`Work.Cohomology.ezChainB_sum_cycle`: if `c` is a `p`-cycle of `X` and `d` a `q`-cycle of `Y`,
then the Eilenberg–Zilber shuffle sum

`∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b`

is a `(p+q)`-cycle of `X ⊗ Y`.

The proof splits `∂(EZ(c ⊗ d))` into the `a`-side `ezA` and the `b`-side `ezB` (the pointwise
shuffle identity `EZG.ezChainB_sbdry_gen`), and each side is killed by the corresponding cycle
hypothesis (`ezA_sum_cycle_zero`, and `ezB_sum_cycle_zero` from
`Submission.Work.Cohomology.ezB_sum_cycle_zero`).  The degenerate cases `p = 0` and `q = 0` are
handled separately with the pointwise identities `EZClean.row0_shuffle` and
`EZClean.col0_shuffle` together with the linear maps `ezChain0` and `ezChain1`.
-/
import Mathlib
import Submission.Work.Cohomology.EZShuffle
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.EZShuffleGen
import Submission.Work.Cohomology.EZClassify
import Submission.Work.Cohomology.EZAssembly
import Submission.Work.Cohomology.EZTensor
import Submission.Work.Cohomology.EZG.cnt_succAbove
import Submission.Work.Cohomology.EZG.cnt_cross
import Submission.Work.Cohomology.EZG.cntB_cross
import Submission.Work.Cohomology.EZG.cnt_cands_lt
import Submission.Work.Cohomology.EZG.ezChainB_sbdry_gen
import Submission.Work.Cohomology.EZClean.row0_shuffle
import Submission.Work.Cohomology.EZClean.col0_shuffle
import Submission.Work.Cohomology.ezB_sum_cycle_zero

open CategoryTheory Simplicial Opposite
open scoped MonoidalCategory

namespace Work.Cohomology

noncomputable section

variable {X Y : SSet.{0}}

/-! ### The `a`-side summand of the shuffle boundary

For `A : Finset (Fin ((P+1)+Q))` with `A.card = P` (an `a`-shuffle of the pair `(P+1, Q)`) and
`i : Fin (P+2)`, `ezH P Q a b A hA i` is the simplex of the `a`-side: the shuffle of the `i`-th
face `δᵢ a` of `a` with `b`. -/
def ezH (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌))
    (A : Finset (Fin ((P+1)+Q))) (hA : A.card = P) (i : Fin (P+2)) :
    (X ⊗ Y).obj (op ⦋(P+1)+Q⦌) :=
  (X.map (shA A (le_of_eq hA)).op (X.δ i a), Y.map (shB A (by have := hA; omega)).op b)

lemma ezA_eq_sum (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    ezA P Q a b
      = ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
          ∑ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P},
            (sgnA A.1 : ℚ) • Finsupp.single (ezH P Q a b A.1 A.2 i) (1 : ℚ) := rfl

/-- Factoring a scalar out of a triple sum. -/
lemma sum_sum_sum_smul_factor {α ι κ M : Type*} [AddCommMonoid M] [Module ℚ M]
    {u : Finset α} {s : Finset ι} {t : Finset κ} (r : ℚ) (z : α → ℚ) (x : ι → κ → ℚ)
    (G : α → ι → κ → M) :
    (∑ i ∈ u, ∑ a ∈ s, ∑ b ∈ t, ((x a b * z i) * r) • G i a b)
      = r • ∑ i ∈ u, z i • ∑ a ∈ s, ∑ b ∈ t, x a b • G i a b := by
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

set_option maxHeartbeats 1600000 in
/-- **The `a`-side of the shuffle identity vanishes on cycles.** -/
theorem ezA_sum_cycle_zero (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (d : Submission.Cohomology.SChain Y ℚ (Q+1))
    (hc : Submission.Cohomology.sbdry X ℚ P c = 0) :
    (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezA P Q a b) = 0 := by
  classical
  have h2 : ∀ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P},
      (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
        ∑ a ∈ c.support, ∑ b ∈ d.support,
          (c a * d b) • Finsupp.single (ezH P Q a b A.1 A.2 i) (1 : ℚ)) = 0 := by
    intro A
    set Φ : X.obj (op ⦋P⦌) × Y.obj (op ⦋Q+1⦌) →
        X.obj (op ⦋(P+1)+Q⦌) × Y.obj (op ⦋(P+1)+Q⦌) :=
      Prod.map (X.map (shA A.1 (le_of_eq A.2)).op)
               (Y.map (shB A.1 (by have := A.2; omega)).op) with hΦ
    have hsingle : ∀ (i : Fin (P+2)) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)),
        (c a * d b) • Finsupp.single (ezH P Q a b A.1 A.2 i) (1 : ℚ)
          = (c a * d b) • Finsupp.mapDomain Φ (Finsupp.single (X.δ i a, b) (1 : ℚ)) := by
      intro i a b
      rw [Finsupp.mapDomain_single]
      rfl
    have hterm : ∀ i : Fin (P+2),
        (∑ a ∈ c.support, ∑ b ∈ d.support,
          (c a * d b) • Finsupp.single (ezH P Q a b A.1 A.2 i) (1 : ℚ))
        = Finsupp.mapDomain Φ (ezTens (Finsupp.mapDomain (X.δ i) c) d) := by
      intro i
      have hstep1 :
          (∑ a ∈ c.support, ∑ b ∈ d.support,
            (c a * d b) • Finsupp.single (ezH P Q a b A.1 A.2 i) (1 : ℚ))
            = ∑ a ∈ c.support, ∑ b ∈ d.support,
                (c a * d b) • Finsupp.mapDomain Φ (Finsupp.single (X.δ i a, b) (1 : ℚ)) :=
        Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => hsingle i a b
      have hstep2 :
          (∑ a ∈ c.support, ∑ b ∈ d.support,
              (c a * d b) • Finsupp.mapDomain Φ (Finsupp.single (X.δ i a, b) (1 : ℚ)))
            = Finsupp.mapDomain Φ (∑ a ∈ c.support, ∑ b ∈ d.support,
                (c a * d b) • Finsupp.single (X.δ i a, b) (1 : ℚ)) :=
        (mapDomain_sum_sum_smul (F := Φ) (s := c.support) (t := d.support)
          (r := fun a b => c a * d b)
          (y := fun a b => Finsupp.single (X.δ i a, b) (1 : ℚ))).symm
      have hstep3 :
          Finsupp.mapDomain Φ (∑ a ∈ c.support, ∑ b ∈ d.support,
              (c a * d b) • Finsupp.single (X.δ i a, b) (1 : ℚ))
            = Finsupp.mapDomain Φ (ezTens (Finsupp.mapDomain (X.δ i) c) d) :=
        congrArg (Finsupp.mapDomain Φ)
          (ezTens_mapDomain_double_sum (φ := X.δ i) (e := c) (f := d)).symm
      rw [hstep1, hstep2, hstep3]
    rw [show (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
            ∑ a ∈ c.support, ∑ b ∈ d.support,
              (c a * d b) • Finsupp.single (ezH P Q a b A.1 A.2 i) (1 : ℚ))
          = ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
              Finsupp.mapDomain Φ (ezTens (Finsupp.mapDomain (X.δ i) c) d) from
        Finset.sum_congr rfl fun i _ =>
          congrArg (fun x => (-1 : ℚ) ^ (i : ℕ) • x) (hterm i)]
    rw [← mapDomain_sum_smul (F := Φ) (s := Finset.univ)
      (r := fun i : Fin (P+2) => (-1 : ℚ) ^ (i : ℕ))
      (y := fun i => ezTens (Finsupp.mapDomain (X.δ i) c) d)]
    rw [← ezTens_sum_smul_left (s := Finset.univ)
      (r := fun i : Fin (P+2) => (-1 : ℚ) ^ (i : ℕ))
      (e := fun i => Finsupp.mapDomain (X.δ i) c) (f := d)]
    rw [← sbdry_eq_sum_mapDomain X P c, hc, ezTens_zero_left, Finsupp.mapDomain_zero]
    rfl
  have hexp : (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezA P Q a b)
      = ∑ a ∈ c.support, ∑ b ∈ d.support, ∑ i : Fin (P+2),
          ∑ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P},
            (((c a * d b) * (-1 : ℚ) ^ (i : ℕ)) * (sgnA A.1 : ℚ)) •
              Finsupp.single (ezH P Q a b A.1 A.2 i) (1 : ℚ) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [ezA_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [smul_smul]
  rw [hexp, sum_sum_sum_sum_comm]
  refine Finset.sum_eq_zero fun A _ => ?_
  rw [sum_sum_sum_smul_factor]
  rw [h2 A, smul_zero]

/-! ### Sum manipulations for the degenerate cases -/

/-- Distributing a scalar factor over a summand. -/
lemma smul_add_smul_comm {M : Type*} [AddCommMonoid M] [Module ℚ M] (c r : ℚ) (x y : M) :
    c • (x + r • y) = c • x + r • (c • y) := by
  rw [smul_add, smul_smul]
  congr 1
  rw [smul_smul, mul_comm]

/-- Factoring a scalar out of a double sum of a sum. -/
lemma sum_sum_smul_add_smul {α β M : Type*} [AddCommMonoid M] [Module ℚ M]
    {s : Finset α} {t : Finset β} (r : ℚ) (x y : α → β → M) (c : α → β → ℚ) :
    (∑ a ∈ s, ∑ b ∈ t, c a b • (x a b + r • y a b))
      = (∑ a ∈ s, ∑ b ∈ t, c a b • x a b) + r • (∑ a ∈ s, ∑ b ∈ t, c a b • y a b) := by
  have h1 : (∑ a ∈ s, ∑ b ∈ t, c a b • (x a b + r • y a b))
      = ∑ a ∈ s, ∑ b ∈ t, (c a b • x a b + r • (c a b • y a b)) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      smul_add_smul_comm (c a b) r (x a b) (y a b)
  rw [h1]
  have h2 : (∑ a ∈ s, ∑ b ∈ t, (c a b • x a b + r • (c a b • y a b)))
      = (∑ a ∈ s, ∑ b ∈ t, c a b • x a b)
        + (∑ a ∈ s, ∑ b ∈ t, r • (c a b • y a b)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
  rw [h2, sum_sum_smul_factor]

/-- Commuting a two-level sum with its scalar coefficients. -/
lemma sum_smul_sum_smul_comm {α ι M : Type*} [AddCommMonoid M] [Module ℚ M]
    {s : Finset α} {u : Finset ι} (r : α → ℚ) (z : ι → ℚ) (G : α → ι → M) :
    (∑ b ∈ s, r b • ∑ j ∈ u, z j • G b j) = ∑ j ∈ u, z j • ∑ b ∈ s, r b • G b j := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ =>
    congrArg (fun t => t • G b j) (mul_comm (r b) (z j))

/-- Rotating a threefold sum: `∑ a ∑ b ∑ i` becomes `∑ b ∑ i ∑ a`. -/
lemma sum3_rotate {α β ι M : Type*} [AddCommMonoid M]
    {s : Finset α} {t : Finset β} {u : Finset ι} (f : α → β → ι → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ i ∈ u, f a b i) = ∑ b ∈ t, ∑ i ∈ u, ∑ a ∈ s, f a b i := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- A linear map commutes with a finite linear combination. -/
lemma map_sum_smul {M N ι : Type*} [AddCommMonoid M] [Module ℚ M] [AddCommMonoid N] [Module ℚ N]
    (f : M →ₗ[ℚ] N) (s : Finset ι) (r : ι → ℚ) (x : ι → M) :
    f (∑ i ∈ s, r i • x i) = ∑ i ∈ s, r i • f (x i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul f (r i) (x i)

/-- Factoring two scalars out of a double sum. -/
lemma sum_sum_smul_factor_three {ι κ M : Type*} [AddCommMonoid M] [Module ℚ M]
    {t : Finset ι} {u : Finset κ} (r : ℚ) (z : ι → ℚ) (c : κ → ℚ) (H : ι → κ → M) :
    (∑ i ∈ t, ∑ a ∈ u, ((c a * r) * z i) • H i a) = r • ∑ i ∈ t, z i • ∑ a ∈ u, c a • H i a := by
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  congr 1
  ring

/-! ### The degenerate cases `p = 0` and `q = 0` -/

/-- The `(0,q)`-Eilenberg–Zilber shuffle map, linear in the chain of `Y`. -/
def ezChain0 (q : ℕ) (a : X.obj (op ⦋0⦌)) :
    Submission.Cohomology.SChain Y ℚ q →ₗ[ℚ] ((X ⊗ Y).obj (op ⦋0+q⦌) →₀ ℚ) :=
  Finsupp.lsum ℚ fun b =>
    LinearMap.toSpanSingleton ℚ ((X ⊗ Y).obj (op ⦋0+q⦌) →₀ ℚ)
      (ezChainB (p := 0) (q := q) a b)

lemma ezChain0_apply (q : ℕ) (a : X.obj (op ⦋0⦌)) (d : Submission.Cohomology.SChain Y ℚ q) :
    ezChain0 q a d = ∑ b ∈ d.support, d b • ezChainB (p := 0) (q := q) a b := by
  rw [ezChain0, Finsupp.lsum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun b _ =>
    LinearMap.toSpanSingleton_apply ℚ ((X ⊗ Y).obj (op ⦋0+q⦌) →₀ ℚ) _ _

lemma ezChain0_mapDomain (Q : ℕ) (a : X.obj (op ⦋0⦌)) (j : Fin (Q+2))
    (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    ezChain0 Q a (Finsupp.mapDomain (Y.δ j) d)
      = ∑ b ∈ d.support, d b • ezChainB (p := 0) (q := Q) a (Y.δ j b) := by
  rw [ezChain0, Finsupp.lsum_apply]
  rw [Finsupp.sum_mapDomain_index (f := Y.δ j) (s := d)
    (h := fun b m => (LinearMap.toSpanSingleton ℚ ((X ⊗ Y).obj (op ⦋0+Q⦌) →₀ ℚ)
      (ezChainB (p := 0) (q := Q) a b)) m)
    (fun b => by rw [map_zero]) (fun b x y => by rw [map_add])]
  rw [Finsupp.sum]
  exact Finset.sum_congr rfl fun b _ =>
    LinearMap.toSpanSingleton_apply ℚ ((X ⊗ Y).obj (op ⦋0+Q⦌) →₀ ℚ) _ _

lemma sbdry_row0 (Q : ℕ) (c : Submission.Cohomology.SChain X ℚ 0)
    (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    Submission.Cohomology.sbdry (X ⊗ Y) ℚ (0+Q)
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := 0) (q := Q+1) a b)
      = ∑ a ∈ c.support, c a • ezChain0 Q a (Submission.Cohomology.sbdry Y ℚ Q d) := by
  classical
  have hstep : Submission.Cohomology.sbdry (X ⊗ Y) ℚ (0+Q)
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := 0) (q := Q+1) a b)
      = ∑ a ∈ c.support, c a • (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
            ∑ b ∈ d.support, d b • ezChainB (p := 0) (q := Q) a (Y.δ j b)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun b _ =>
      map_smul (Submission.Cohomology.sbdry (X ⊗ Y) ℚ (0+Q)) (c a * d b)
        (ezChainB (p := 0) (q := Q+1) a b))]
    have h1 : (∑ b ∈ d.support, (c a * d b) •
          Submission.Cohomology.sbdry (X ⊗ Y) ℚ (0+Q) (ezChainB (p := 0) (q := Q+1) a b))
        = ∑ b ∈ d.support, (c a * d b) • (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
            ezChainB (p := 0) (q := Q) a (Y.δ j b)) :=
      Finset.sum_congr rfl fun b _ =>
        congrArg (fun x => (c a * d b) • x) (EZClean.row0_shuffle Q X Y a b)
    rw [h1]
    rw [Finset.sum_congr rfl (fun b _ =>
      (smul_smul (c a) (d b) (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
        ezChainB (p := 0) (q := Q) a (Y.δ j b))).symm)]
    rw [← Finset.smul_sum]
    exact congrArg (fun x => c a • x)
      (sum_smul_sum_smul_comm (s := d.support) (u := Finset.univ)
        (r := fun b => d b) (z := fun j : Fin (Q+2) => (-1 : ℚ) ^ (j : ℕ))
        (G := fun b j => ezChainB (p := 0) (q := Q) a (Y.δ j b)))
  rw [hstep]
  refine Finset.sum_congr rfl fun a _ => congrArg (fun x => c a • x) ?_
  have h3 : (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
        ∑ b ∈ d.support, d b • ezChainB (p := 0) (q := Q) a (Y.δ j b))
      = ∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
        ezChain0 Q a (Finsupp.mapDomain (Y.δ j) d) :=
    Finset.sum_congr rfl fun j _ => congrArg (fun x => (-1 : ℚ) ^ (j : ℕ) • x)
      (ezChain0_mapDomain Q a j d).symm
  rw [h3]
  rw [show (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) • ezChain0 Q a (Finsupp.mapDomain (Y.δ j) d))
      = ezChain0 Q a (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) • Finsupp.mapDomain (Y.δ j) d) from
    (map_sum_smul (ezChain0 Q a) Finset.univ (fun j : Fin (Q+2) => (-1 : ℚ) ^ (j : ℕ))
      (fun j : Fin (Q+2) => Finsupp.mapDomain (Y.δ j) d)).symm]
  rw [← sbdry_eq_sum_mapDomain Y Q d]

/-- The `(p,0)`-Eilenberg–Zilber shuffle map, linear in the chain of `X`. -/
def ezChain1 (p : ℕ) (b : Y.obj (op ⦋0⦌)) :
    Submission.Cohomology.SChain X ℚ p →ₗ[ℚ] ((X ⊗ Y).obj (op ⦋p+0⦌) →₀ ℚ) :=
  Finsupp.lsum ℚ fun a =>
    LinearMap.toSpanSingleton ℚ ((X ⊗ Y).obj (op ⦋p+0⦌) →₀ ℚ)
      (ezChainB (p := p) (q := 0) a b)

lemma ezChain1_apply (p : ℕ) (b : Y.obj (op ⦋0⦌)) (c : Submission.Cohomology.SChain X ℚ p) :
    ezChain1 p b c = ∑ a ∈ c.support, c a • ezChainB (p := p) (q := 0) a b := by
  rw [ezChain1, Finsupp.lsum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun a _ =>
    LinearMap.toSpanSingleton_apply ℚ ((X ⊗ Y).obj (op ⦋p+0⦌) →₀ ℚ) _ _

lemma ezChain1_mapDomain (P : ℕ) (b : Y.obj (op ⦋0⦌)) (i : Fin (P+2))
    (c : Submission.Cohomology.SChain X ℚ (P+1)) :
    ezChain1 P b (Finsupp.mapDomain (X.δ i) c)
      = ∑ a ∈ c.support, c a • ezChainB (p := P) (q := 0) (X.δ i a) b := by
  rw [ezChain1, Finsupp.lsum_apply]
  rw [Finsupp.sum_mapDomain_index (f := X.δ i) (s := c)
    (h := fun a m => (LinearMap.toSpanSingleton ℚ ((X ⊗ Y).obj (op ⦋P+0⦌) →₀ ℚ)
      (ezChainB (p := P) (q := 0) a b)) m)
    (fun a => by rw [map_zero]) (fun a x y => by rw [map_add])]
  rw [Finsupp.sum]
  exact Finset.sum_congr rfl fun a _ =>
    LinearMap.toSpanSingleton_apply ℚ ((X ⊗ Y).obj (op ⦋P+0⦌) →₀ ℚ) _ _

lemma sbdry_col0 (P : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (d : Submission.Cohomology.SChain Y ℚ 0) :
    Submission.Cohomology.sbdry (X ⊗ Y) ℚ P
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := P+1) (q := 0) a b)
      = ∑ b ∈ d.support, d b • ezChain1 P b (Submission.Cohomology.sbdry X ℚ P c) := by
  classical
  have hstep : Submission.Cohomology.sbdry (X ⊗ Y) ℚ P
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := P+1) (q := 0) a b)
      = ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
            ezChainB (p := P) (q := 0) (X.δ i a) b) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun b _ =>
      map_smul (Submission.Cohomology.sbdry (X ⊗ Y) ℚ P) (c a * d b)
        (ezChainB (p := P+1) (q := 0) a b))]
    exact Finset.sum_congr rfl fun b _ =>
      congrArg (fun x => (c a * d b) • x) (EZClean.col0_shuffle P X Y a b)
  rw [hstep]
  have h2 : (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
        (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) • ezChainB (p := P) (q := 0) (X.δ i a) b))
      = ∑ a ∈ c.support, ∑ b ∈ d.support, ∑ i : Fin (P+2),
          ((c a * d b) * (-1 : ℚ) ^ (i : ℕ)) • ezChainB (p := P) (q := 0) (X.δ i a) b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  rw [h2, sum3_rotate]
  have h3 : (∑ b ∈ d.support, ∑ i : Fin (P+2), ∑ a ∈ c.support,
        ((c a * d b) * (-1 : ℚ) ^ (i : ℕ)) • ezChainB (p := P) (q := 0) (X.δ i a) b)
      = ∑ b ∈ d.support, d b • ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
          ∑ a ∈ c.support, c a • ezChainB (p := P) (q := 0) (X.δ i a) b :=
    Finset.sum_congr rfl fun b _ =>
      sum_sum_smul_factor_three (t := Finset.univ) (u := c.support) (r := d b)
        (z := fun i : Fin (P+2) => (-1 : ℚ) ^ (i : ℕ)) (c := fun a => c a)
        (H := fun i a => ezChainB (p := P) (q := 0) (X.δ i a) b)
  rw [h3]
  have h4 : (∑ b ∈ d.support, d b • ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
        ∑ a ∈ c.support, c a • ezChainB (p := P) (q := 0) (X.δ i a) b)
      = ∑ b ∈ d.support, d b • ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
        ezChain1 P b (Finsupp.mapDomain (X.δ i) c) :=
    Finset.sum_congr rfl fun b _ => congrArg (fun x => d b • x)
      (Finset.sum_congr rfl fun i _ => congrArg (fun x => (-1 : ℚ) ^ (i : ℕ) • x)
        (ezChain1_mapDomain P b i c).symm)
  rw [h4]
  refine Finset.sum_congr rfl fun b _ => congrArg (fun x => d b • x) ?_
  rw [show (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) • ezChain1 P b (Finsupp.mapDomain (X.δ i) c))
      = ezChain1 P b (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) • Finsupp.mapDomain (X.δ i) c) from
    (map_sum_smul (ezChain1 P b) Finset.univ (fun i : Fin (P+2) => (-1 : ℚ) ^ (i : ℕ))
      (fun i : Fin (P+2) => Finsupp.mapDomain (X.δ i) c)).symm]
  rw [← sbdry_eq_sum_mapDomain X P c]

/-! ### The Eilenberg–Zilber shuffle lemma for chains -/

theorem ezChainB_sum_cycle {X Y : SSet.{0}} {p q : ℕ} (c : Submission.Cohomology.SChain X ℚ p)
    (d : Submission.Cohomology.SChain Y ℚ q)
    (hc : c ∈ Submission.Cohomology.chainCycles X ℚ p)
    (hd : d ∈ Submission.Cohomology.chainCycles Y ℚ q) :
    (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • Work.Cohomology.ezChainB a b)
      ∈ Submission.Cohomology.chainCycles
          (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q) := by
  rcases p with _ | P
  · rcases q with _ | Q
    · exact Submodule.mem_top
    · change (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b) ∈
        Submission.Cohomology.chainCycles (X ⊗ Y) ℚ ((0+Q)+1)
      rw [Submission.Cohomology.mem_chainCycles_succ, Work.Cohomology.sbdry_row0 Q c d,
        (Submission.Cohomology.mem_chainCycles_succ (n := Q)).mp hd]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [map_zero, smul_zero]
  · rcases q with _ | Q
    · change (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b) ∈
        Submission.Cohomology.chainCycles (X ⊗ Y) ℚ (P+1)
      rw [Submission.Cohomology.mem_chainCycles_succ, Work.Cohomology.sbdry_col0 P c d,
        (Submission.Cohomology.mem_chainCycles_succ (n := P)).mp hc]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [map_zero, smul_zero]
    · change (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b) ∈
        Submission.Cohomology.chainCycles (X ⊗ Y) ℚ (((P+1)+Q)+1)
      rw [Submission.Cohomology.mem_chainCycles_succ]
      have hpt : ∀ (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)),
          Submission.Cohomology.sbdry (X ⊗ Y) ℚ ((P+1)+Q)
              (ezChainB (p := P+1) (q := Q+1) a b)
            = ezA P Q a b + (-1 : ℚ) ^ (P+1) • ezB P Q a b :=
        fun a b => EZG.ezChainB_sbdry_gen P Q X Y a b
      have h1 : Submission.Cohomology.sbdry (X ⊗ Y) ℚ ((P+1)+Q)
            (∑ a ∈ c.support, ∑ b ∈ d.support,
              (c a * d b) • ezChainB (p := P+1) (q := Q+1) a b)
          = ∑ a ∈ c.support, ∑ b ∈ d.support,
              (c a * d b) • (ezA P Q a b + (-1 : ℚ) ^ (P+1) • ezB P Q a b) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_sum]
        rw [Finset.sum_congr rfl (fun b _ =>
          map_smul (Submission.Cohomology.sbdry (X ⊗ Y) ℚ ((P+1)+Q)) (c a * d b)
            (ezChainB (p := P+1) (q := Q+1) a b))]
        rw [Finset.sum_congr rfl (fun b _ =>
          congrArg (fun x => (c a * d b) • x) (hpt a b))]
      have h2 : (∑ a ∈ c.support, ∑ b ∈ d.support,
            (c a * d b) • (ezA P Q a b + (-1 : ℚ) ^ (P+1) • ezB P Q a b))
          = (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezA P Q a b)
            + (-1 : ℚ) ^ (P+1) •
              (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezB P Q a b) :=
        sum_sum_smul_add_smul ((-1 : ℚ) ^ (P+1)) (fun a b => ezA P Q a b)
          (fun a b => ezB P Q a b) (fun a b => c a * d b)
      rw [h1, h2,
        ezA_sum_cycle_zero P Q c d ((Submission.Cohomology.mem_chainCycles_succ (n := P)).mp hc),
        ezB_sum_cycle_zero P Q c d ((Submission.Cohomology.mem_chainCycles_succ (n := Q)).mp hd)]
      simp

end

end Work.Cohomology
