import Mathlib
import Submission.Work.Cohomology.EZShuffle
import Submission.Work.Cohomology.EZShuffleGen
import Submission.Work.Cohomology.EZClassify
import Submission.Work.Cohomology.EZAssembly
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.EZG.ezChainB_sbdry_gen
import Submission.Work.Cohomology.EZClean.row0_shuffle
import Submission.Work.Cohomology.EZClean.col0_shuffle

open CategoryTheory Simplicial Opposite
open scoped MonoidalCategory

namespace Work.Cohomology.EZClean

noncomputable section

variable {X Y : SSet.{0}}

/-! ## General sum manipulations -/

lemma sum_smul_sum_comm {α ι M : Type*} [AddCommMonoid M] [Module ℚ M]
    {s : Finset α} {t : Finset ι} (c : α → ℚ) (sc : ι → ℚ) (Z : α → ι → M) :
    (∑ a ∈ s, c a • ∑ i ∈ t, sc i • Z a i) = ∑ i ∈ t, sc i • ∑ a ∈ s, c a • Z a i := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

lemma double_smul_sum {α ι M : Type*} [AddCommMonoid M] [Module ℚ M]
    {s : Finset α} {t : Finset ι} (c : α → ℚ) (e : ι → ℚ) (Z : α → ι → M) :
    (∑ a ∈ s, ∑ i ∈ t, (c a * e i) • Z a i) = ∑ i ∈ t, e i • ∑ a ∈ s, c a • Z a i := by
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

lemma double_smul_sum_left {α ι M : Type*} [AddCommMonoid M] [Module ℚ M]
    {s : Finset α} {t : Finset ι} (c : α → ℚ) (e : ι → ℚ) (Z : α → ι → M) :
    (∑ a ∈ s, ∑ i ∈ t, (c a * e i) • Z a i) = ∑ a ∈ s, c a • ∑ i ∈ t, e i • Z a i := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]

lemma sum_sum_add_smul {α ι M : Type*} [AddCommMonoid M] [Module ℚ M]
    {s : Finset α} {t : Finset ι} (X Y : α → ι → M) (r : ℚ) :
    (∑ a ∈ s, ∑ i ∈ t, (X a i + r • Y a i))
      = (∑ a ∈ s, ∑ i ∈ t, X a i) + r • (∑ a ∈ s, ∑ i ∈ t, Y a i) := by
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]

lemma sum3_comm {α ι κ M : Type*} [AddCommMonoid M]
    {s : Finset α} {t : Finset ι} {u : Finset κ} (f : α → ι → κ → M) :
    (∑ a ∈ s, ∑ i ∈ t, ∑ k ∈ u, f a i k) = ∑ k ∈ u, ∑ a ∈ s, ∑ i ∈ t, f a i k := by
  have h1 : (∑ a ∈ s, ∑ i ∈ t, ∑ k ∈ u, f a i k)
      = ∑ a ∈ s, ∑ k ∈ u, ∑ i ∈ t, f a i k := by
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  rw [h1, Finset.sum_comm]

lemma sum_sum_smul_sum {α ι κ M : Type*} [AddCommMonoid M] [Module ℚ M]
    {s : Finset α} {t : Finset ι} {u : Finset κ} (Z : α → ι → κ → M)
    (c : α → ℚ) (e : ι → ℚ) (sc : κ → ℚ) :
    (∑ a ∈ s, ∑ i ∈ t, (c a * e i) • (∑ k ∈ u, sc k • Z a i k))
      = ∑ k ∈ u, sc k • ∑ a ∈ s, ∑ i ∈ t, (c a * e i) • Z a i k := by
  have hL : (∑ a ∈ s, ∑ i ∈ t, (c a * e i) • (∑ k ∈ u, sc k • Z a i k))
      = ∑ a ∈ s, ∑ i ∈ t, ∑ k ∈ u, ((c a * e i) * sc k) • Z a i k := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
  have hR : (∑ k ∈ u, sc k • ∑ a ∈ s, ∑ i ∈ t, (c a * e i) • Z a i k)
      = ∑ k ∈ u, ∑ a ∈ s, ∑ i ∈ t, ((c a * e i) * sc k) • Z a i k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  rw [hL, hR, ← sum3_comm (f := fun a i k => ((c a * e i) * sc k) • Z a i k)]

lemma ezc_sbdry_single_one (S : SSet.{0}) (n : ℕ) (σ : S.obj (op ⦋n+1⦌)) :
    Submission.Cohomology.sbdry S ℚ n (Finsupp.single σ 1)
      = ∑ k : Fin (n+2), (-1 : ℚ) ^ (k : ℕ) • Finsupp.single (S.δ k σ) 1 := by
  rw [Submission.Cohomology.sbdry_single]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul, mul_one, Finsupp.smul_single]
  congr 1
  push_cast
  ring

lemma sbdry_eq_sum (S : SSet.{0}) (n : ℕ) :
    Submission.Cohomology.sbdry S ℚ n
      = ∑ k : Fin (n+2), (-1 : ℚ) ^ (k : ℕ) • Finsupp.lmapDomain ℚ ℚ (S.δ k) := by
  rw [Submission.Cohomology.sbdry]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Int.cast_smul_eq_zsmul ℚ]
  congr 1
  push_cast
  ring

/-! ## The a-side and b-side summands -/

def ezA' {P Q : ℕ} (x : X.obj (op ⦋P⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    Submission.Cohomology.SChain (X ⊗ Y) ℚ ((P+1)+Q) :=
  ∑ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P},
    (sgnA A.1 : ℚ) •
      Finsupp.single
        (X.map (shA A.1 (le_of_eq A.2)).op x,
         Y.map (shB A.1 (by have := A.2; omega)).op b) 1

def ezB' {P Q : ℕ} (a : X.obj (op ⦋P+1⦌)) (y : Y.obj (op ⦋Q⦌)) :
    Submission.Cohomology.SChain (X ⊗ Y) ℚ ((P+1)+Q) :=
  ∑ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P+1},
    (sgnA A.1 : ℚ) •
      Finsupp.single
        (X.map (shA A.1 (by have := A.2; omega)).op a,
         Y.map (shB A.1 (by have := A.2; omega)).op y) 1

lemma ezA_eq (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    ezA P Q a b = ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) • ezA' (P := P) (Q := Q) (X.δ i a) b :=
  rfl

lemma ezB_eq (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    ezB P Q a b = ∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) • ezB' (P := P) (Q := Q) a (Y.δ j b) :=
  rfl

/-! ## The a-side chain maps -/

def ezAchain (P Q : ℕ) (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    Submission.Cohomology.SChain X ℚ (P+1) →ₗ[ℚ]
      Submission.Cohomology.SChain (X ⊗ Y) ℚ ((P+1)+Q) :=
  Finsupp.linearCombination ℚ (fun a : X.obj (op ⦋P+1⦌) =>
    Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋Q+1⦌) => ezA P Q a b) d)

lemma ezAchain_apply (P Q : ℕ) (d : Submission.Cohomology.SChain Y ℚ (Q+1))
    (c : Submission.Cohomology.SChain X ℚ (P+1)) :
    ezAchain P Q d c
      = ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezA P Q a b := by
  show (Finsupp.linearCombination ℚ (fun a : X.obj (op ⦋P+1⦌) =>
      Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋Q+1⦌) => ezA P Q a b) d) c) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul]

def ezAchain' (P Q : ℕ) (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    Submission.Cohomology.SChain X ℚ P →ₗ[ℚ]
      Submission.Cohomology.SChain (X ⊗ Y) ℚ ((P+1)+Q) :=
  Finsupp.linearCombination ℚ (fun x : X.obj (op ⦋P⦌) =>
    Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋Q+1⦌) => ezA' (P := P) (Q := Q) x b) d)

lemma ezAchain'_single (P Q : ℕ) (d : Submission.Cohomology.SChain Y ℚ (Q+1))
    (x : X.obj (op ⦋P⦌)) :
    ezAchain' P Q d (Finsupp.single x 1)
      = ∑ b ∈ d.support, d b • ezA' (P := P) (Q := Q) x b := by
  show (Finsupp.linearCombination ℚ (fun x : X.obj (op ⦋P⦌) =>
      Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋Q+1⦌) => ezA' (P := P) (Q := Q) x b) d)
      (Finsupp.single x 1)) = _
  rw [Finsupp.linearCombination_single, one_smul, Finsupp.linearCombination_apply, Finsupp.sum]

lemma ezAchain_single (P Q : ℕ) (d : Submission.Cohomology.SChain Y ℚ (Q+1))
    (a : X.obj (op ⦋P+1⦌)) :
    ezAchain P Q d (Finsupp.single a 1) = ∑ b ∈ d.support, d b • ezA P Q a b := by
  show (Finsupp.linearCombination ℚ (fun a : X.obj (op ⦋P+1⦌) =>
      Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋Q+1⦌) => ezA P Q a b) d)
      (Finsupp.single a 1)) = _
  rw [Finsupp.linearCombination_single, one_smul, Finsupp.linearCombination_apply, Finsupp.sum]

lemma ezAchain'_sbdry_single (P Q : ℕ) (d : Submission.Cohomology.SChain Y ℚ (Q+1))
    (σ : X.obj (op ⦋P+1⦌)) :
    ezAchain' P Q d (Submission.Cohomology.sbdry X ℚ P (Finsupp.single σ 1))
      = ∑ b ∈ d.support, d b • ezA P Q σ b := by
  rw [ezc_sbdry_single_one, map_sum]
  simp_rw [map_smul, ezAchain'_single]
  rw [show (∑ b ∈ d.support, d b • ezA P Q σ b)
      = ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
          ∑ b ∈ d.support, d b • ezA' (P := P) (Q := Q) (X.δ i σ) b from ?_]
  · trans ∑ b ∈ d.support, d b •
        (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) • ezA' (P := P) (Q := Q) (X.δ i σ) b)
    · exact Finset.sum_congr rfl fun b _ => by rw [ezA_eq]
    · rw [sum_smul_sum_comm (s := d.support) (t := (Finset.univ : Finset (Fin (P+2))))
        (fun b => d b) (fun i => (-1 : ℚ) ^ (i : ℕ))
        (fun b i => ezA' (P := P) (Q := Q) (X.δ i σ) b)]

lemma ezAchain_sbdry (P Q : ℕ) (d : Submission.Cohomology.SChain Y ℚ (Q+1))
    (c : Submission.Cohomology.SChain X ℚ (P+1)) :
    ezAchain P Q d c = ezAchain' P Q d (Submission.Cohomology.sbdry X ℚ P c) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | single σ r =>
      rw [show Finsupp.single σ r = r • Finsupp.single σ 1 by simp]
      simp only [map_smul]
      rw [ezAchain_single, ezAchain'_sbdry_single]

/-! ## The b-side chain maps -/

def ezBchain (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1)) :
    Submission.Cohomology.SChain Y ℚ (Q+1) →ₗ[ℚ]
      Submission.Cohomology.SChain (X ⊗ Y) ℚ ((P+1)+Q) :=
  Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋Q+1⦌) =>
    Finsupp.linearCombination ℚ (fun a : X.obj (op ⦋P+1⦌) => ezB P Q a b) c)

lemma ezBchain_apply (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    ezBchain P Q c d = ∑ b ∈ d.support, ∑ a ∈ c.support, (d b * c a) • ezB P Q a b := by
  show (Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋Q+1⦌) =>
      Finsupp.linearCombination ℚ (fun a : X.obj (op ⦋P+1⦌) => ezB P Q a b) c) d) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul]

lemma ezBchain_double (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    ezBchain P Q c d
      = ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezB P Q a b := by
  rw [ezBchain_apply, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]

def ezBchain' (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1)) :
    Submission.Cohomology.SChain Y ℚ Q →ₗ[ℚ]
      Submission.Cohomology.SChain (X ⊗ Y) ℚ ((P+1)+Q) :=
  Finsupp.linearCombination ℚ (fun y : Y.obj (op ⦋Q⦌) =>
    Finsupp.linearCombination ℚ (fun a : X.obj (op ⦋P+1⦌) => ezB' (P := P) (Q := Q) a y) c)

lemma ezBchain'_single (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (y : Y.obj (op ⦋Q⦌)) :
    ezBchain' P Q c (Finsupp.single y 1)
      = ∑ a ∈ c.support, c a • ezB' (P := P) (Q := Q) a y := by
  show (Finsupp.linearCombination ℚ (fun y : Y.obj (op ⦋Q⦌) =>
      Finsupp.linearCombination ℚ (fun a : X.obj (op ⦋P+1⦌) => ezB' (P := P) (Q := Q) a y) c)
      (Finsupp.single y 1)) = _
  rw [Finsupp.linearCombination_single, one_smul, Finsupp.linearCombination_apply, Finsupp.sum]

lemma ezBchain_single (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (b : Y.obj (op ⦋Q+1⦌)) :
    ezBchain P Q c (Finsupp.single b 1) = ∑ a ∈ c.support, c a • ezB P Q a b := by
  show (Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋Q+1⦌) =>
      Finsupp.linearCombination ℚ (fun a : X.obj (op ⦋P+1⦌) => ezB P Q a b) c)
      (Finsupp.single b 1)) = _
  rw [Finsupp.linearCombination_single, one_smul, Finsupp.linearCombination_apply, Finsupp.sum]

lemma ezBchain'_sbdry_single (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (τ : Y.obj (op ⦋Q+1⦌)) :
    ezBchain' P Q c (Submission.Cohomology.sbdry Y ℚ Q (Finsupp.single τ 1))
      = ∑ a ∈ c.support, c a • ezB P Q a τ := by
  rw [ezc_sbdry_single_one, map_sum]
  simp_rw [map_smul, ezBchain'_single]
  rw [show (∑ a ∈ c.support, c a • ezB P Q a τ)
      = ∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
          ∑ a ∈ c.support, c a • ezB' (P := P) (Q := Q) a (Y.δ j τ) from ?_]
  · trans ∑ a ∈ c.support, c a •
        (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) • ezB' (P := P) (Q := Q) a (Y.δ j τ))
    · exact Finset.sum_congr rfl fun a _ => by rw [ezB_eq]
    · rw [sum_smul_sum_comm (s := c.support) (t := (Finset.univ : Finset (Fin (Q+2))))
        (fun a => c a) (fun j => (-1 : ℚ) ^ (j : ℕ))
        (fun a j => ezB' (P := P) (Q := Q) a (Y.δ j τ))]

lemma ezBchain_sbdry (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    ezBchain P Q c d = ezBchain' P Q c (Submission.Cohomology.sbdry Y ℚ Q d) := by
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | single σ r =>
      rw [show Finsupp.single σ r = r • Finsupp.single σ 1 by simp]
      simp only [map_smul]
      rw [ezBchain_single, ezBchain'_sbdry_single]

/-! ## The uniform `ezx`/`ezy` maps -/

def ezx (p q : ℕ) (d : Submission.Cohomology.SChain Y ℚ q) :
    Submission.Cohomology.SChain X ℚ p →ₗ[ℚ]
      Submission.Cohomology.SChain (X ⊗ Y) ℚ (p+q) :=
  Finsupp.linearCombination ℚ (fun x : X.obj (op ⦋p⦌) =>
    Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋q⦌) =>
      ezChainB (p := p) (q := q) x b) d)

def ezy (p q : ℕ) (c : Submission.Cohomology.SChain X ℚ p) :
    Submission.Cohomology.SChain Y ℚ q →ₗ[ℚ]
      Submission.Cohomology.SChain (X ⊗ Y) ℚ (p+q) :=
  Finsupp.linearCombination ℚ (fun y : Y.obj (op ⦋q⦌) =>
    Finsupp.linearCombination ℚ (fun x : X.obj (op ⦋p⦌) =>
      ezChainB (p := p) (q := q) x y) c)

lemma ezx_apply (p q : ℕ) (d : Submission.Cohomology.SChain Y ℚ q)
    (e : Submission.Cohomology.SChain X ℚ p) :
    ezx p q d e = ∑ x ∈ e.support, ∑ b ∈ d.support, (e x * d b) •
      ezChainB (p := p) (q := q) x b := by
  show (Finsupp.linearCombination ℚ (fun x : X.obj (op ⦋p⦌) =>
      Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋q⦌) =>
        ezChainB (p := p) (q := q) x b) d) e) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul]

lemma ezy_apply (p q : ℕ) (c : Submission.Cohomology.SChain X ℚ p)
    (e : Submission.Cohomology.SChain Y ℚ q) :
    ezy p q c e = ∑ y ∈ e.support, ∑ x ∈ c.support, (e y * c x) •
      ezChainB (p := p) (q := q) x y := by
  show (Finsupp.linearCombination ℚ (fun y : Y.obj (op ⦋q⦌) =>
      Finsupp.linearCombination ℚ (fun x : X.obj (op ⦋p⦌) =>
        ezChainB (p := p) (q := q) x y) c) e) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul]

lemma ezy_mapDomain (p q : ℕ) (c : Submission.Cohomology.SChain X ℚ p) {Q : ℕ}
    (f : Y.obj (op ⦋Q⦌) → Y.obj (op ⦋q⦌)) (d : Submission.Cohomology.SChain Y ℚ Q) :
    ezy p q c (Finsupp.mapDomain f d)
      = ∑ b ∈ d.support, d b • ∑ x ∈ c.support, c x • ezChainB (p := p) (q := q) x (f b) := by
  have h : ezy p q c (Finsupp.mapDomain f d)
      = Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋Q⦌) =>
          Finsupp.linearCombination ℚ (fun x : X.obj (op ⦋p⦌) =>
            ezChainB (p := p) (q := q) x (f b)) c) d := by
    show (Finsupp.linearCombination ℚ (fun y : Y.obj (op ⦋q⦌) =>
        Finsupp.linearCombination ℚ (fun x : X.obj (op ⦋p⦌) =>
          ezChainB (p := p) (q := q) x y) c)) (Finsupp.mapDomain f d) = _
    rw [Finsupp.linearCombination_mapDomain]
    rfl
  rw [h, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finsupp.linearCombination_apply, Finsupp.sum]

lemma ezx_mapDomain (p q : ℕ) (d : Submission.Cohomology.SChain Y ℚ q) {P : ℕ}
    (f : X.obj (op ⦋P⦌) → X.obj (op ⦋p⦌)) (e : Submission.Cohomology.SChain X ℚ P) :
    ezx p q d (Finsupp.mapDomain f e)
      = ∑ a ∈ e.support, e a • ∑ b ∈ d.support, d b • ezChainB (p := p) (q := q) (f a) b := by
  have h : ezx p q d (Finsupp.mapDomain f e)
      = Finsupp.linearCombination ℚ (fun a : X.obj (op ⦋P⦌) =>
          Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋q⦌) =>
            ezChainB (p := p) (q := q) (f a) b) d) e := by
    show (Finsupp.linearCombination ℚ (fun x : X.obj (op ⦋p⦌) =>
        Finsupp.linearCombination ℚ (fun b : Y.obj (op ⦋q⦌) =>
          ezChainB (p := p) (q := q) x b) d)) (Finsupp.mapDomain f e) = _
    rw [Finsupp.linearCombination_mapDomain]
    rfl
  rw [h, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.linearCombination_apply, Finsupp.sum]

/-! ## The chain-level boundary identities -/

theorem sbdry_ezsum_gen (P Q : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    Submission.Cohomology.sbdry (X ⊗ Y) ℚ ((P+1)+Q)
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := P+1) (q := Q+1) a b)
      = ezAchain P Q d c + (-1 : ℚ) ^ (P+1) • ezBchain P Q c d := by
  have hpt : ∀ a b, (c a * d b) • (ezA P Q a b + (-1 : ℚ) ^ (P+1) • ezB P Q a b)
      = (c a * d b) • ezA P Q a b + (-1 : ℚ) ^ (P+1) • ((c a * d b) • ezB P Q a b) := by
    intro a b
    rw [smul_add]
    simp only [smul_smul]
    rw [mul_comm (c a * d b) ((-1 : ℚ) ^ (P+1))]
  calc Submission.Cohomology.sbdry (X ⊗ Y) ℚ ((P+1)+Q)
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := P+1) (q := Q+1) a b)
      = ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          Submission.Cohomology.sbdry (X ⊗ Y) ℚ ((P+1)+Q) (ezChainB (p := P+1) (q := Q+1) a b) := by
        simp only [map_sum, map_smul]
    _ = ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          (ezA P Q a b + (-1 : ℚ) ^ (P+1) • ezB P Q a b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Work.Cohomology.EZG.ezChainB_sbdry_gen]
    _ = (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezA P Q a b)
          + (-1 : ℚ) ^ (P+1) •
            (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezB P Q a b) := by
        simp_rw [hpt]
        rw [sum_sum_add_smul]
    _ = ezAchain P Q d c + (-1 : ℚ) ^ (P+1) • ezBchain P Q c d := by
        rw [← ezAchain_apply, ← ezBchain_double]

theorem sbdry_ezsum_row0 (Q : ℕ) (c : Submission.Cohomology.SChain X ℚ 0)
    (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    Submission.Cohomology.sbdry (X ⊗ Y) ℚ (0+Q)
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := 0) (q := Q+1) a b)
      = ezy 0 Q c (Submission.Cohomology.sbdry Y ℚ Q d) := by
  have h1 : Submission.Cohomology.sbdry (X ⊗ Y) ℚ (0+Q)
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := 0) (q := Q+1) a b)
      = ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) • ezChainB (p := 0) (q := Q) a (Y.δ j b)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, Work.Cohomology.EZClean.row0_shuffle]
  have h2 : ezy 0 Q c (Submission.Cohomology.sbdry Y ℚ Q d)
      = ∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
          ezy 0 Q c (Finsupp.mapDomain (Y.δ j) d) := by
    rw [sbdry_eq_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Finsupp.lmapDomain_apply]
  have h3 : (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) • ezChainB (p := 0) (q := Q) a (Y.δ j b)))
      = ∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
          ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
            ezChainB (p := 0) (q := Q) a (Y.δ j b) :=
    sum_sum_smul_sum (fun a b j => ezChainB (p := 0) (q := Q) a (Y.δ j b))
      (fun a => c a) (fun b => d b) (fun j => (-1 : ℚ) ^ (j : ℕ))
  rw [h1, h2, h3]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [show (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
        ezChainB (p := 0) (q := Q) a (Y.δ j b))
      = ∑ b ∈ d.support, d b • ∑ a ∈ c.support, c a •
        ezChainB (p := 0) (q := Q) a (Y.δ j b) from
    double_smul_sum (fun a => c a) (fun b => d b)
      (fun a b => ezChainB (p := 0) (q := Q) a (Y.δ j b))]
  exact (ezy_mapDomain 0 Q c (Y.δ j) d).symm

theorem sbdry_ezsum_col0 (P : ℕ) (c : Submission.Cohomology.SChain X ℚ (P+1))
    (d : Submission.Cohomology.SChain Y ℚ 0) :
    Submission.Cohomology.sbdry (X ⊗ Y) ℚ P
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := P+1) (q := 0) a b)
      = ezx P 0 d (Submission.Cohomology.sbdry X ℚ P c) := by
  have h1 : Submission.Cohomology.sbdry (X ⊗ Y) ℚ P
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB (p := P+1) (q := 0) a b)
      = ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) • ezChainB (p := P) (q := 0) (X.δ i a) b) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, Work.Cohomology.EZClean.col0_shuffle]
  have h2 : ezx P 0 d (Submission.Cohomology.sbdry X ℚ P c)
      = ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
          ezx P 0 d (Finsupp.mapDomain (X.δ i) c) := by
    rw [sbdry_eq_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Finsupp.lmapDomain_apply]
  have h3 : (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) • ezChainB (p := P) (q := 0) (X.δ i a) b))
      = ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
          ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
            ezChainB (p := P) (q := 0) (X.δ i a) b :=
    sum_sum_smul_sum (fun a b i => ezChainB (p := P) (q := 0) (X.δ i a) b)
      (fun a => c a) (fun b => d b) (fun i => (-1 : ℚ) ^ (i : ℕ))
  rw [h1, h2, h3]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [show (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
        ezChainB (p := P) (q := 0) (X.δ i a) b)
      = ∑ a ∈ c.support, c a • ∑ b ∈ d.support, d b •
        ezChainB (p := P) (q := 0) (X.δ i a) b from
    double_smul_sum_left (fun a => c a) (fun b => d b)
      (fun a b => ezChainB (p := P) (q := 0) (X.δ i a) b)]
  exact (ezx_mapDomain P 0 d (X.δ i) c).symm

end

end Work.Cohomology.EZClean

namespace Work.Cohomology

theorem ezChainB_sum_cycle_clean {X Y : SSet.{0}} {p q : ℕ}
    (c : Submission.Cohomology.SChain X ℚ p) (d : Submission.Cohomology.SChain Y ℚ q)
    (hc : c ∈ Submission.Cohomology.chainCycles X ℚ p)
    (hd : d ∈ Submission.Cohomology.chainCycles Y ℚ q) :
    (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • Work.Cohomology.ezChainB a b)
      ∈ Submission.Cohomology.chainCycles
          (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q) := by
  rcases p with _ | P
  · rcases q with _ | Q
    · exact Submodule.mem_top
    · show (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b) ∈
        Submission.Cohomology.chainCycles (X ⊗ Y) ℚ ((0+Q)+1)
      rw [Submission.Cohomology.mem_chainCycles_succ, Work.Cohomology.EZClean.sbdry_ezsum_row0,
          (Submission.Cohomology.mem_chainCycles_succ (n := Q)).mp hd, map_zero]
  · rcases q with _ | Q
    · rw [Submission.Cohomology.mem_chainCycles_succ, Work.Cohomology.EZClean.sbdry_ezsum_col0,
          (Submission.Cohomology.mem_chainCycles_succ (n := P)).mp hc, map_zero]
    · show (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b) ∈
        Submission.Cohomology.chainCycles (X ⊗ Y) ℚ (((P+1)+Q)+1)
      rw [Submission.Cohomology.mem_chainCycles_succ, Work.Cohomology.EZClean.sbdry_ezsum_gen,
          Work.Cohomology.EZClean.ezAchain_sbdry, Work.Cohomology.EZClean.ezBchain_sbdry,
          (Submission.Cohomology.mem_chainCycles_succ (n := P)).mp hc,
          (Submission.Cohomology.mem_chainCycles_succ (n := Q)).mp hd]
      simp



end Work.Cohomology
