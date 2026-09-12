import Mathlib
import Submission.Szemeredi.Removal.Defs

/-!
# Hypergraph systems, discrepancy, and the energy-increment lemma

This file sets up Tao's hypergraph-system formalism (arXiv:math/0503572, §2) and
proves the **energy increment lemma**: if a set `E_e` has large discrepancy with
respect to a product of σ-algebras on the `(|e|-1)`-faces of `e`, then refining
those σ-algebras by at most one generator each strictly increases the energy, by
at least `δ²`.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false

namespace Szemeredi.Removal

/-- The ambient point space of a hypergraph system: one vertex per index. -/
abbrev Pt {ι : Type*} (V : ι → Type*) : Type _ := (i : ι) → V i

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-- The σ-algebra of sets determined by the coordinates indexed by `e`. -/
noncomputable def coord (e : Finset ι) : SigAlg (Pt V) where
  block := fun x => Finset.univ.filter (fun y => ∀ i ∈ e, y i = x i)
  mem_block := by
    intro x
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i _ => rfl⟩
  block_eq := by
    intro x y hy
    rw [Finset.mem_filter] at hy
    ext z
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨-, hz⟩
      exact ⟨Finset.mem_univ _, fun i hi => (hz i hi).trans (hy.2 i hi)⟩
    · rintro ⟨-, hz⟩
      exact ⟨Finset.mem_univ _, fun i hi => (hz i hi).trans (hy.2 i hi).symm⟩

@[simp] theorem coord_block (e : Finset ι) (x : Pt V) :
    (coord (V := V) e).block x = Finset.univ.filter (fun y => ∀ i ∈ e, y i = x i) := rfl

theorem coord_isMeas_iff {e : Finset ι} {E : Finset (Pt V)} :
    (coord (V := V) e).IsMeas E ↔ ∀ x y, (∀ i ∈ e, y i = x i) → (y ∈ E ↔ x ∈ E) := by
  constructor
  · intro h x y hxy
    have hmem : y ∈ (coord (V := V) e).block x := by
      rw [coord_block, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hxy⟩
    exact (SigAlg.isMeas_iff _ E).mp h x y hmem
  · intro h
    refine (SigAlg.isMeas_iff _ E).mpr ?_
    intro x y hy
    rw [coord_block, Finset.mem_filter] at hy
    exact h x y hy.2

/-- The `(|e|-1)`-element subsets of `e` (the boundary `∂e`). -/
def del (e : Finset ι) : Finset (Finset ι) := e.powerset.filter (fun f => f.card + 1 = e.card)

theorem mem_del {e f : Finset ι} : f ∈ del e ↔ f ⊆ e ∧ f.card + 1 = e.card := by
  simp only [del, Finset.mem_filter, Finset.mem_powerset]

/-- `E_e` is pseudorandom at level `δ` with respect to `B`. -/
def Pseudorandom (e : Finset ι) (Ee : Finset (Pt V)) (B : SigAlg (Pt V)) (δ : ℝ) : Prop :=
  ∀ Ex : Finset ι → Finset (Pt V), (∀ f ∈ del e, (coord (V := V) f).IsMeas (Ex f)) →
    |avg (fun x => (indicator Ee x - B.condExp (indicator Ee) x) *
      ∏ f ∈ del e, indicator (Ex f) x)| ≤ δ

/-- **Energy increment lemma** (Tao, arXiv:math/0503572, Lemma 2.2): if `E_e` is not
`δ`-pseudorandom with respect to the join of the σ-algebras `B f`, then one can
refine each `B f` by at most one generator so that the energy of `E_e` increases
by at least `δ²`. -/
theorem energy_increment {e : Finset ι} {Ee : Finset (Pt V)} {B : Finset ι → SigAlg (Pt V)}
    {δ : ℝ} (hB : ∀ f ∈ del e, (B f).Refines (coord (V := V) f)) (hδ : 0 < δ)
    (hnot : ¬ Pseudorandom (V := V) e Ee (SigAlg.iInf B (del e)) δ) :
    ∃ B' : Finset ι → SigAlg (Pt V),
      (∀ f ∈ del e, (B' f).Refines (coord (V := V) f)) ∧
      (∀ f ∈ del e, (B f).Refines (B' f)) ∧
      (∀ f ∈ del e, (B' f).complexity ≤ (B f).complexity + 1) ∧
      (SigAlg.iInf B (del e)).energy (indicator Ee) + δ ^ 2 ≤
        (SigAlg.iInf B' (del e)).energy (indicator Ee) := by
  classical
  rw [Pseudorandom] at hnot
  push_neg at hnot
  obtain ⟨Ex, hExmeas, hval⟩ := hnot
  let B' : Finset ι → SigAlg (Pt V) := fun f => (B f).addSet (Ex f)
  let P : SigAlg (Pt V) := SigAlg.iInf B (del e)
  let P' : SigAlg (Pt V) := SigAlg.iInf B' (del e)
  let g : Pt V → ℝ := fun x => ∏ f ∈ del e, indicator (Ex f) x
  let f0 : Pt V → ℝ := indicator Ee
  have hP'ref : P.Refines P' :=
    SigAlg.Refines.iInf_mono (fun f hf => SigAlg.Refines.addSet (B f) (Ex f))
  have hMeasP' : ∀ f ∈ del e, P'.IsMeas (Ex f) := by
    intro f hf
    exact SigAlg.IsMeas.of_refines (SigAlg.Refines.iInf B' (del e) f hf)
      (SigAlg.isMeas_addSet_self (B f) (Ex f))
  have hgconst : ∀ x y, y ∈ P'.block x → g y = g x := by
    intro x y hy
    refine Finset.prod_congr rfl (fun f hf => ?_)
    have hiff := (SigAlg.isMeas_iff P' (Ex f)).mp (hMeasP' f hf) x y hy
    unfold indicator
    by_cases hx : x ∈ Ex f
    · rw [if_pos (hiff.mpr hx), if_pos hx]
    · rw [if_neg (fun h => hx (hiff.mp h)), if_neg hx]
  have h0 : avg (fun x => (f0 x - P'.condExp f0 x) * g x) = 0 := by
    rw [show (fun x : Pt V => (f0 x - P'.condExp f0 x) * g x)
        = (fun x : Pt V => g x * (f0 x - P'.condExp f0 x)) from
      funext (fun x => mul_comm _ _)]
    exact SigAlg.avg_mul_sub_condExp P' hgconst
  have hkey : avg (fun x => (P'.condExp f0 x - P.condExp f0 x) * g x)
      = avg (fun x => (f0 x - P.condExp f0 x) * g x) := by
    have hsum : avg (fun x => (P'.condExp f0 x - P.condExp f0 x) * g x)
        + avg (fun x => (f0 x - P'.condExp f0 x) * g x)
        = avg (fun x => (f0 x - P.condExp f0 x) * g x) := by
      rw [← SigAlg.avg_add]
      congr 1
      funext x
      ring
    rw [h0, add_zero] at hsum
    exact hsum
  have hlarge : δ < |avg (fun x => (P'.condExp f0 x - P.condExp f0 x) * g x)| := by
    rw [hkey]
    exact hval
  have hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := by
    intro x
    constructor
    · exact Finset.prod_nonneg (fun f hf => SigAlg.indicator_nonneg _ x)
    · exact Finset.prod_le_one (fun f hf => SigAlg.indicator_nonneg _ x)
        (fun f hf => SigAlg.indicator_le_one _ x)
  have hcs : (avg (fun x => (P'.condExp f0 x - P.condExp f0 x) * g x)) ^ 2
      ≤ avg (fun x => (P'.condExp f0 x - P.condExp f0 x) ^ 2) := by
    have h1 := SigAlg.avg_mul_sq_le (fun x => P'.condExp f0 x - P.condExp f0 x) g
    have h2 : avg (fun x => (g x) ^ 2) ≤ 1 :=
      SigAlg.avg_sq_le_avg_of_le_one (fun x => (hg01 x).1) (fun x => (hg01 x).2)
    have h3 : 0 ≤ avg (fun x => (P'.condExp f0 x - P.condExp f0 x) ^ 2) :=
      SigAlg.avg_nonneg (fun x => sq_nonneg _)
    calc (avg (fun x => (P'.condExp f0 x - P.condExp f0 x) * g x)) ^ 2
        ≤ avg (fun x => (P'.condExp f0 x - P.condExp f0 x) ^ 2) * avg (fun x => (g x) ^ 2) := h1
      _ ≤ avg (fun x => (P'.condExp f0 x - P.condExp f0 x) ^ 2) * 1 := by gcongr
      _ = avg (fun x => (P'.condExp f0 x - P.condExp f0 x) ^ 2) := mul_one _
  have hsq : δ ^ 2 < avg (fun x => (P'.condExp f0 x - P.condExp f0 x) ^ 2) := by
    have h1 : δ ^ 2 < (avg (fun x => (P'.condExp f0 x - P.condExp f0 x) * g x)) ^ 2 := by
      have h2 : |δ| < |avg (fun x => (P'.condExp f0 x - P.condExp f0 x) * g x)| := by
        rwa [abs_of_pos hδ]
      calc δ ^ 2 = |δ| ^ 2 := by rw [sq_abs]
        _ < |avg (fun x => (P'.condExp f0 x - P.condExp f0 x) * g x)| ^ 2 :=
            pow_lt_pow_left₀ h2 (abs_nonneg δ) (by norm_num)
        _ = (avg (fun x => (P'.condExp f0 x - P.condExp f0 x) * g x)) ^ 2 := by rw [sq_abs]
    linarith
  have hpyth := SigAlg.energy_eq_energy_add hP'ref f0
  refine ⟨B', fun f hf => SigAlg.Refines.addSet_of_isMeas (hB f hf) (hExmeas f hf),
    fun f hf => SigAlg.Refines.addSet _ _, fun f hf => SigAlg.complexity_addSet_le _ _,
    ?_⟩
  linarith [hpyth]

end Szemeredi.Removal
