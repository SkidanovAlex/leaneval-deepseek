import Mathlib
import Submission.Szemeredi.Removal.Increment

/-!
# The dichotomy between structure and pseudorandomness (Tao, arXiv:math/0503572, Lemma 2.3)

If a family of sets `E_e` indexed by a `d`-uniform hypergraph `H` fails to be
pseudorandom relative to a family of σ-algebras on the boundary `∂H`, then one can
refine those σ-algebras (by a bounded number of generators) so that either the
energy of each `E_e` increases by less than `ε²` and all the `E_e` become
`δ`-pseudorandom, or some `E_e` has energy increase at least `ε²`.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-- The boundary `∂H := ⋃_{e ∈ H} ∂e` of a family of index sets. -/
def bdry (H : Finset (Finset ι)) : Finset (Finset ι) := H.biUnion del

theorem mem_bdry {H : Finset (Finset ι)} {f : Finset ι} :
    f ∈ bdry H ↔ ∃ e ∈ H, f ∈ del e := by
  simp [bdry]

theorem energy_mono {P P' : SigAlg (Pt V)} (h : P.Refines P') (f : Pt V → ℝ) :
    P.energy f ≤ P'.energy f := by
  have hp := energy_eq_energy_add h f
  have hnn : 0 ≤ avg (fun x => (P'.condExp f x - P.condExp f x) ^ 2) :=
    avg_nonneg (fun x => sq_nonneg _)
  linarith

theorem energy_le_one_indicator (P : SigAlg (Pt V)) (E : Finset (Pt V)) :
    P.energy (indicator E) ≤ 1 :=
  (energy_le_avg_sq P _).trans
    (avg_sq_le_avg_of_le_one (fun x => indicator_nonneg E x) (fun x => indicator_le_one E x))

theorem card_isMeas_le (P : SigAlg (Pt V)) :
    Nat.card {E : Finset (Pt V) // P.IsMeas E} ≤ 2 ^ P.atoms.card := by
  classical
  rw [Nat.card_eq_fintype_card]
  let f : {E : Finset (Pt V) // P.IsMeas E} → ↥(P.atoms.powerset) := fun E =>
    ⟨P.atoms.filter (fun s => s ⊆ (E : Finset (Pt V))),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  have hinj : Function.Injective f := by
    intro E F h
    have h' : P.atoms.filter (fun s => s ⊆ (E : Finset (Pt V)))
        = P.atoms.filter (fun s => s ⊆ (F : Finset (Pt V))) := congrArg Subtype.val h
    have hEF : (E : Finset (Pt V)) = F := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hsub : P.block x ⊆ (E : Finset (Pt V)) := E.2 x hx
        have hmem : P.block x ∈ P.atoms.filter (fun s => s ⊆ (E : Finset (Pt V))) :=
          Finset.mem_filter.mpr ⟨P.block_mem_atoms x, hsub⟩
        rw [h'] at hmem
        exact (Finset.mem_filter.mp hmem).2 (P.mem_block x)
      · intro x hx
        have hsub : P.block x ⊆ (F : Finset (Pt V)) := F.2 x hx
        have hmem : P.block x ∈ P.atoms.filter (fun s => s ⊆ (F : Finset (Pt V))) :=
          Finset.mem_filter.mpr ⟨P.block_mem_atoms x, hsub⟩
        rw [← h'] at hmem
        exact (Finset.mem_filter.mp hmem).2 (P.mem_block x)
    exact Subtype.ext hEF
  calc Fintype.card {E : Finset (Pt V) // P.IsMeas E}
      ≤ Fintype.card ↥(P.atoms.powerset) := Fintype.card_le_of_injective f hinj
    _ = (P.atoms.powerset).card := Fintype.card_coe _
    _ = 2 ^ P.atoms.card := Finset.card_powerset _

/-- The total energy of all the measurable sets `E_e`, `e ∈ H`. -/noncomputable def energySum (H : Finset (Finset ι)) (Be : Finset ι → SigAlg (Pt V))
    (P : Finset ι → SigAlg (Pt V)) : ℝ := by
  classical
  exact ∑ e ∈ H, ∑ Ee : Finset (Pt V),
    (if (Be e).IsMeas Ee then (SigAlg.iInf P (del e)).energy (indicator Ee) else 0)

theorem energySum_mono {H : Finset (Finset ι)} {Be : Finset ι → SigAlg (Pt V)}
    {P P' : Finset ι → SigAlg (Pt V)}
    (h : ∀ e ∈ H, ∀ f ∈ del e, (P f).Refines (P' f)) : energySum H Be P ≤ energySum H Be P' := by
  classical
  unfold energySum
  refine Finset.sum_le_sum (fun e he => Finset.sum_le_sum (fun Ee _ => ?_))
  by_cases hEe : (Be e).IsMeas Ee
  · rw [if_pos hEe, if_pos hEe]
    exact energy_mono (SigAlg.Refines.iInf_mono (fun f hf => h e he f hf)) _
  · rw [if_neg hEe, if_neg hEe]

theorem energySum_le {H : Finset (Finset ι)} {Be : Finset ι → SigAlg (Pt V)}
    {m : ℕ} (hm : ∀ e ∈ H, (Be e).complexity ≤ m) (P : Finset ι → SigAlg (Pt V)) :
    energySum H Be P ≤ (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) := by
  classical
  have hterm : ∀ e ∈ H, (∑ Ee : Finset (Pt V),
        (if (Be e).IsMeas Ee then (SigAlg.iInf P (del e)).energy (indicator Ee) else 0))
      ≤ (2 : ℝ) ^ (2 ^ m) := by
    intro e he
    calc ∑ Ee : Finset (Pt V),
          (if (Be e).IsMeas Ee then (SigAlg.iInf P (del e)).energy (indicator Ee) else 0)
        ≤ ∑ Ee : Finset (Pt V), (if (Be e).IsMeas Ee then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum (fun Ee _ => ?_)
          by_cases h : (Be e).IsMeas Ee
          · rw [if_pos h, if_pos h]; exact energy_le_one_indicator _ _
          · rw [if_neg h, if_neg h]
      _ = (↑(Finset.univ.filter (fun Ee => (Be e).IsMeas Ee)).card : ℝ) := by
          rw [Finset.sum_boole]
      _ = (Nat.card {E : Finset (Pt V) // (Be e).IsMeas E} : ℝ) := by
          congr 1
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ ≤ (2 : ℝ) ^ (2 ^ m) := by
          have hc : Nat.card {E : Finset (Pt V) // (Be e).IsMeas E} ≤ 2 ^ (2 ^ m) :=
            calc Nat.card {E : Finset (Pt V) // (Be e).IsMeas E}
                ≤ 2 ^ (Be e).atoms.card := card_isMeas_le _
              _ ≤ 2 ^ (2 ^ (Be e).complexity) :=
                  Nat.pow_le_pow_right (by norm_num) (atoms_card_le_pow_complexity _)
              _ ≤ 2 ^ (2 ^ m) := Nat.pow_le_pow_right (by norm_num)
                  (Nat.pow_le_pow_right (by norm_num) (hm e he))
          exact_mod_cast hc
  calc energySum H Be P
      = ∑ e ∈ H, ∑ Ee : Finset (Pt V),
          (if (Be e).IsMeas Ee then (SigAlg.iInf P (del e)).energy (indicator Ee) else 0) := rfl
    _ ≤ ∑ _e ∈ H, (2 : ℝ) ^ (2 ^ m) := Finset.sum_le_sum hterm
    _ = (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) := by
        rw [Finset.sum_const, nsmul_eq_mul]

theorem add_sum_le_sum_of_le_of_le_one {κ : Type*} [DecidableEq κ] {s : Finset κ}
    {f g : κ → ℝ} {a : κ}
    {c : ℝ} (ha : a ∈ s) (h : ∀ x ∈ s, f x ≤ g x) (h1 : f a + c ≤ g a) :
    (∑ x ∈ s, f x) + c ≤ ∑ x ∈ s, g x := by
  have h2 : ∑ x ∈ s.erase a, f x ≤ ∑ x ∈ s.erase a, g x :=
    Finset.sum_le_sum (fun x _ => h x (Finset.mem_of_mem_erase ‹x ∈ s.erase a›))
  linarith [Finset.sum_erase_add s f ha, Finset.sum_erase_add s g ha]


theorem card_filter_eq_natCard (p : Finset (Pt V) → Prop) [DecidablePred p] :
    (↑(Finset.univ.filter p).card : ℝ) = (Nat.card {x : Finset (Pt V) // p x} : ℝ) := by
  classical
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_ite_mul_card (p : Finset (Pt V) → Prop) [DecidablePred p] (c : ℝ) :
    (∑ x : Finset (Pt V), (if p x then c else 0))
      = (↑(Finset.univ.filter p).card : ℝ) * c := by
  classical
  calc ∑ x : Finset (Pt V), (if p x then c else 0)
      = ∑ x : Finset (Pt V), (if p x then (1 : ℝ) else 0) * c := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        by_cases h : p x <;> simp [h]
    _ = (∑ x : Finset (Pt V), (if p x then (1 : ℝ) else 0)) * c := by
        rw [Finset.sum_mul]
    _ = (↑(Finset.univ.filter p).card : ℝ) * c := by
        rw [Finset.sum_boole]

/-- `Ebe1 H Be B ε P` says: refining `B` to `P` increases the energy of every
`B_e`-measurable set by less than `ε²`.  This is the "structural" alternative of
the dichotomy. -/
def Ebe1 (H : Finset (Finset ι)) (Be B : Finset ι → SigAlg (Pt V)) (ε : ℝ)
    (P : Finset ι → SigAlg (Pt V)) : Prop :=
  ∀ e ∈ H, ∀ Ee : Finset (Pt V), (Be e).IsMeas Ee →
    (SigAlg.iInf P (del e)).energy (indicator Ee) <
      (SigAlg.iInf B (del e)).energy (indicator Ee) + ε ^ 2

/-- `Ebe2 H Be δ P` says: every `B_e`-measurable set is `δ`-pseudorandom with
respect to the boundary σ-algebras of `P`.  This is the "random" alternative. -/
def Ebe2 (H : Finset (Finset ι)) (Be : Finset ι → SigAlg (Pt V)) (δ : ℝ)
    (P : Finset ι → SigAlg (Pt V)) : Prop :=
  ∀ e ∈ H, ∀ Ee : Finset (Pt V), (Be e).IsMeas Ee →
    Pseudorandom (V := V) e Ee (SigAlg.iInf P (del e)) δ

/-- The number of refinement steps needed for the dichotomy. -/
noncomputable def dichBound (H : Finset (Finset ι)) (m : ℕ) (ε δ : ℝ) : ℕ :=
  Nat.ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 / δ ^ 2) + 1

theorem not_ebe2 {H : Finset (Finset ι)} {Be : Finset ι → SigAlg (Pt V)} {δ : ℝ}
    {P : Finset ι → SigAlg (Pt V)} (h : ¬ Ebe2 (V := V) H Be δ P) :
    ∃ e ∈ H, ∃ Ee : Finset (Pt V), (Be e).IsMeas Ee ∧
      ¬ Pseudorandom (V := V) e Ee (SigAlg.iInf P (del e)) δ := by
  rw [Ebe2] at h
  push_neg at h
  exact h

/-- **One refinement step** (the engine of the dichotomy).  If `E₀` is not
`δ`-pseudorandom with respect to the boundary σ-algebras of `P`, then one can
refine `P` by at most one generator per boundary index so that the energy of `E₀`
increases by at least `δ²`. -/
theorem dichStep {e₀ : Finset ι} {E₀ : Finset (Pt V)} {Be P : Finset ι → SigAlg (Pt V)}
    {δ : ℝ} (hcoord : ∀ f ∈ del e₀, (P f).Refines (coord (V := V) f))
    (hE₀ : (Be e₀).IsMeas E₀) (hδ : 0 < δ)
    (hnot : ¬ Pseudorandom (V := V) e₀ E₀ (SigAlg.iInf P (del e₀)) δ) :
    ∃ P' : Finset ι → SigAlg (Pt V),
      (∀ f, (P f).Refines (P' f)) ∧
      (∀ f, f ∉ del e₀ → P' f = P f) ∧
      (∀ f ∈ del e₀, (P' f).Refines (coord (V := V) f)) ∧
      (∀ f, (P' f).complexity ≤ (P f).complexity + 1) ∧
      (SigAlg.iInf P (del e₀)).energy (indicator E₀) + δ ^ 2 ≤
        (SigAlg.iInf P' (del e₀)).energy (indicator E₀) := by
  obtain ⟨B', hB'coord, hB'ref, hB'complex, hB'energy⟩ :=
    energy_increment (V := V) (e := e₀) (Ee := E₀) (B := P) hcoord hδ hnot
  refine ⟨fun f => if f ∈ del e₀ then B' f else P f, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    dsimp only
    by_cases hf : f ∈ del e₀
    · rw [if_pos hf]; exact hB'ref f hf
    · rw [if_neg hf]; exact SigAlg.Refines.refl _
  · intro f hf
    dsimp only
    rw [if_neg hf]
  · intro f hf
    dsimp only
    rw [if_pos hf]
    exact hB'coord f hf
  · intro f
    dsimp only
    by_cases hf : f ∈ del e₀
    · rw [if_pos hf]; exact hB'complex f hf
    · rw [if_neg hf]; omega
  · have hblock : ∀ x, (SigAlg.iInf (fun f => if f ∈ del e₀ then B' f else P f) (del e₀)).block x
        = (SigAlg.iInf B' (del e₀)).block x := by
      intro x
      rw [SigAlg.iInf_block, SigAlg.iInf_block]
      exact Finset.inf_congr rfl (fun f hf => by rw [if_pos hf])
    have heq : SigAlg.iInf (fun f => if f ∈ del e₀ then B' f else P f) (del e₀)
        = SigAlg.iInf B' (del e₀) := SigAlg.ext hblock
    rw [heq]
    exact hB'energy

/-- The energy sum increases by at least `δ²` when a single set jumps. -/
theorem energySum_add_le {H : Finset (Finset ι)} {Be P P' : Finset ι → SigAlg (Pt V)}
    {e₀ : Finset ι} {E₀ : Finset (Pt V)} {δ : ℝ}
    (he₀ : e₀ ∈ H) (hE₀ : (Be e₀).IsMeas E₀)
    (hmono : ∀ e ∈ H, ∀ f ∈ del e, (P f).Refines (P' f))
    (hsingle : (SigAlg.iInf P (del e₀)).energy (indicator E₀) + δ ^ 2 ≤
      (SigAlg.iInf P' (del e₀)).energy (indicator E₀)) :
    energySum H Be P + δ ^ 2 ≤ energySum H Be P' := by
  classical
  unfold energySum
  refine add_sum_le_sum_of_le_of_le_one (s := H) he₀ (fun e he => ?_) ?_
  · refine Finset.sum_le_sum (fun Ee _ => ?_)
    by_cases hEe : (Be e).IsMeas Ee
    · rw [if_pos hEe, if_pos hEe]
      exact energy_mono (SigAlg.Refines.iInf_mono (fun f hf => hmono e he f hf)) _
    · rw [if_neg hEe, if_neg hEe]
  · refine add_sum_le_sum_of_le_of_le_one (s := (Finset.univ : Finset (Finset (Pt V))))
      (Finset.mem_univ E₀) (fun Ee _ => ?_) ?_
    · by_cases hEe : (Be e₀).IsMeas Ee
      · rw [if_pos hEe, if_pos hEe]
        exact energy_mono (SigAlg.Refines.iInf_mono (fun f hf => hmono e₀ he₀ f hf)) _
      · rw [if_neg hEe, if_neg hEe]
    · rw [if_pos hE₀, if_pos hE₀]
      exact hsingle

/-- A "bad" state of the iteration: `P` refines both the base family `B` and the
coordinate σ-algebras, its complexity is at most `B`'s plus `n`, the structure
alternative holds and the random alternative fails, and the total energy has
increased by at least `n δ²`. -/
def IsBad (H : Finset (Finset ι)) (Be B : Finset ι → SigAlg (Pt V)) (ε δ : ℝ) (n : ℕ)
    (P : Finset ι → SigAlg (Pt V)) : Prop :=
  (∀ f ∈ bdry H, (B f).Refines (P f)) ∧
  (∀ f ∈ bdry H, (P f).Refines (coord (V := V) f)) ∧
  (∀ f ∈ bdry H, (P f).complexity ≤ (B f).complexity + n) ∧
  Ebe1 (V := V) H Be B ε P ∧ ¬ Ebe2 (V := V) H Be δ P ∧
  energySum H Be B + (n : ℝ) * δ ^ 2 ≤ energySum H Be P

/-- The energy sum is bounded by that of `B` plus the number of measurable sets
times `ε²`, when the structure alternative `Ebe1` holds. -/
theorem energySum_le_of_ebe1 {H : Finset (Finset ι)} {Be B P : Finset ι → SigAlg (Pt V)}
    {m : ℕ} {ε : ℝ} (hm : ∀ e ∈ H, (Be e).complexity ≤ m)
    (h1 : Ebe1 (V := V) H Be B ε P) :
    energySum H Be P ≤ energySum H Be B + (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 := by
  classical
  have hterm : ∀ e ∈ H, (∑ Ee : Finset (Pt V),
        (if (Be e).IsMeas Ee then (SigAlg.iInf P (del e)).energy (indicator Ee) else 0))
      ≤ (∑ Ee : Finset (Pt V),
        (if (Be e).IsMeas Ee then (SigAlg.iInf B (del e)).energy (indicator Ee) else 0))
        + (2 : ℝ) ^ (2 ^ m) * ε ^ 2 := by
    intro e he
    calc ∑ Ee : Finset (Pt V),
          (if (Be e).IsMeas Ee then (SigAlg.iInf P (del e)).energy (indicator Ee) else 0)
        ≤ ∑ Ee : Finset (Pt V),
          ((if (Be e).IsMeas Ee then (SigAlg.iInf B (del e)).energy (indicator Ee) else 0)
            + (if (Be e).IsMeas Ee then ε ^ 2 else 0)) := by
          refine Finset.sum_le_sum (fun Ee _ => ?_)
          by_cases hEe : (Be e).IsMeas Ee
          · rw [if_pos hEe, if_pos hEe, if_pos hEe]
            have hle := h1 e he Ee hEe
            linarith
          · simp [hEe]
      _ = (∑ Ee : Finset (Pt V),
            (if (Be e).IsMeas Ee then (SigAlg.iInf B (del e)).energy (indicator Ee) else 0))
          + ∑ Ee : Finset (Pt V), (if (Be e).IsMeas Ee then ε ^ 2 else 0) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ Ee : Finset (Pt V),
            (if (Be e).IsMeas Ee then (SigAlg.iInf B (del e)).energy (indicator Ee) else 0))
          + (↑(Finset.univ.filter (fun Ee => (Be e).IsMeas Ee)).card : ℝ) * ε ^ 2 := by
          rw [sum_ite_mul_card]
      _ ≤ (∑ Ee : Finset (Pt V),
            (if (Be e).IsMeas Ee then (SigAlg.iInf B (del e)).energy (indicator Ee) else 0))
          + (2 : ℝ) ^ (2 ^ m) * ε ^ 2 := by
          gcongr
          rw [card_filter_eq_natCard]
          exact_mod_cast (calc Nat.card {E : Finset (Pt V) // (Be e).IsMeas E}
                ≤ 2 ^ (Be e).atoms.card := card_isMeas_le _
              _ ≤ 2 ^ (2 ^ (Be e).complexity) :=
                  Nat.pow_le_pow_right (by norm_num) (atoms_card_le_pow_complexity _)
              _ ≤ 2 ^ (2 ^ m) := Nat.pow_le_pow_right (by norm_num)
                  (Nat.pow_le_pow_right (by norm_num) (hm e he)))
  calc energySum H Be P
      = ∑ e ∈ H, ∑ Ee : Finset (Pt V),
          (if (Be e).IsMeas Ee then (SigAlg.iInf P (del e)).energy (indicator Ee) else 0) := rfl
    _ ≤ ∑ e ∈ H, ((∑ Ee : Finset (Pt V),
          (if (Be e).IsMeas Ee then (SigAlg.iInf B (del e)).energy (indicator Ee) else 0))
          + (2 : ℝ) ^ (2 ^ m) * ε ^ 2) := Finset.sum_le_sum hterm
    _ = (∑ e ∈ H, ∑ Ee : Finset (Pt V),
          (if (Be e).IsMeas Ee then (SigAlg.iInf B (del e)).energy (indicator Ee) else 0))
          + ∑ _e ∈ H, (2 : ℝ) ^ (2 ^ m) * ε ^ 2 := by rw [Finset.sum_add_distrib]
    _ = energySum H Be B + (H.card : ℝ) * ((2 : ℝ) ^ (2 ^ m) * ε ^ 2) := by
          rw [energySum, Finset.sum_const, nsmul_eq_mul]
    _ = energySum H Be B + (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 := by ring

/-- One step of the iteration: from a bad state at level `n` (with `n + 1 ≤ N`)
produce a bad state at level `n + 1`, using the two negated alternatives. -/
theorem isBad_step {H : Finset (Finset ι)} {Be B : Finset ι → SigAlg (Pt V)} {ε δ : ℝ}
    {N : ℕ} {n : ℕ} {P : Finset ι → SigAlg (Pt V)}
    (hbad : IsBad (V := V) H Be B ε δ n P) (hδ : 0 < δ) (hn : n + 1 ≤ N)
    (hEbe1' : ∀ P' : Finset ι → SigAlg (Pt V),
        (∀ f ∈ bdry H, (B f).Refines (P' f)) →
        (∀ f ∈ bdry H, (P' f).Refines (coord (V := V) f)) →
        (∀ f ∈ bdry H, (P' f).complexity ≤ (B f).complexity + N) →
        Ebe1 (V := V) H Be B ε P')
    (hEbe2' : ∀ P' : Finset ι → SigAlg (Pt V),
        (∀ f ∈ bdry H, (B f).Refines (P' f)) →
        (∀ f ∈ bdry H, (P' f).Refines (coord (V := V) f)) →
        Ebe1 (V := V) H Be B ε P' → ¬ Ebe2 (V := V) H Be δ P') :
    ∃ P' : Finset ι → SigAlg (Pt V), IsBad (V := V) H Be B ε δ (n + 1) P' := by
  obtain ⟨hrefB, hrefC, hcx, h1, h2, henergy⟩ := hbad
  obtain ⟨e₀, he₀, E₀, hE₀, hnot⟩ :=
    not_ebe2 (V := V) (H := H) (Be := Be) (δ := δ) (P := P) h2
  obtain ⟨P', hrefP, houtside, hrefCP, hcxP, hjump⟩ :=
    dichStep (V := V) (e₀ := e₀) (E₀ := E₀) (Be := Be) (P := P) (δ := δ)
      (fun f hf => hrefC f (mem_bdry.mpr ⟨e₀, he₀, hf⟩)) hE₀ hδ hnot
  have hrefB' : ∀ f ∈ bdry H, (B f).Refines (P' f) := fun f hf => (hrefB f hf).trans (hrefP f)
  have hrefC' : ∀ f ∈ bdry H, (P' f).Refines (coord (V := V) f) := by
    intro f hf
    by_cases hfe : f ∈ del e₀
    · exact hrefCP f hfe
    · rw [houtside f hfe]; exact hrefC f hf
  have hcx' : ∀ f ∈ bdry H, (P' f).complexity ≤ (B f).complexity + (n + 1) := by
    intro f hf
    have h3 := hcxP f
    have h4 := hcx f hf
    omega
  have h1' : Ebe1 (V := V) H Be B ε P' :=
    hEbe1' P' hrefB' hrefC' (fun f hf => le_trans (hcx' f hf) (by omega))
  have h2' : ¬ Ebe2 (V := V) H Be δ P' := hEbe2' P' hrefB' hrefC' h1'
  have henergy' : energySum H Be B + ((n + 1 : ℕ) : ℝ) * δ ^ 2 ≤ energySum H Be P' := by
    have hmono : ∀ e ∈ H, ∀ f ∈ del e, (P f).Refines (P' f) := fun e _ f _ => hrefP f
    have hstep := energySum_add_le (H := H) (Be := Be) (P := P) (P' := P') (e₀ := e₀)
      (E₀ := E₀) (δ := δ) he₀ hE₀ hmono hjump
    push_cast
    linarith
  exact ⟨P', hrefB', hrefC', hcx', h1', h2', henergy'⟩

/-- **The dichotomy between structure and pseudorandomness** (Tao, arXiv:math/0503572,
Lemma 2.3).  Given a family of `B_e`-measurable sets indexed by the `d`-uniform
hypergraph `H`, and σ-algebras `B f` on the boundary refining the coordinate
σ-algebras, either

* there is a refinement `B'` on which every set is `δ`-pseudorandom and no energy
  increases by `ε²`, or
* there is a refinement `B'` with complexity at most `+dichBound H m ε δ` on which
  some set's energy jumps by at least `ε²`. -/
theorem dichotomy {H : Finset (Finset ι)} {Be B : Finset ι → SigAlg (Pt V)} {m : ℕ}
    (hm : ∀ e ∈ H, (Be e).complexity ≤ m)
    (hB : ∀ f ∈ bdry H, (B f).Refines (coord (V := V) f))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (∃ B' : Finset ι → SigAlg (Pt V),
        (∀ f ∈ bdry H, (B f).Refines (B' f)) ∧
        (∀ f ∈ bdry H, (B' f).Refines (coord (V := V) f)) ∧
        Ebe1 (V := V) H Be B ε B' ∧
        Ebe2 (V := V) H Be δ B') ∨
      (∃ B' : Finset ι → SigAlg (Pt V),
        (∀ f ∈ bdry H, (B f).Refines (B' f)) ∧
        (∀ f ∈ bdry H, (B' f).Refines (coord (V := V) f)) ∧
        (∀ f ∈ bdry H, (B' f).complexity ≤ (B f).complexity + dichBound H m ε δ) ∧
        (∃ e ∈ H, ∃ Ee : Finset (Pt V), (Be e).IsMeas Ee ∧
            (SigAlg.iInf B (del e)).energy (indicator Ee) + ε ^ 2 ≤
              (SigAlg.iInf B' (del e)).energy (indicator Ee))) := by
  classical
  set N : ℕ := dichBound H m ε δ with hN
  by_contra hconcl
  rw [not_or] at hconcl
  obtain ⟨hOrInl, hOrInr⟩ := hconcl
  have hEbe2' : ∀ P : Finset ι → SigAlg (Pt V),
      (∀ f ∈ bdry H, (B f).Refines (P f)) →
      (∀ f ∈ bdry H, (P f).Refines (coord (V := V) f)) →
      Ebe1 (V := V) H Be B ε P → ¬ Ebe2 (V := V) H Be δ P :=
    fun P hrB hrC h1 h2 => hOrInl ⟨P, hrB, hrC, h1, h2⟩
  have hEbe1' : ∀ P : Finset ι → SigAlg (Pt V),
      (∀ f ∈ bdry H, (B f).Refines (P f)) →
      (∀ f ∈ bdry H, (P f).Refines (coord (V := V) f)) →
      (∀ f ∈ bdry H, (P f).complexity ≤ (B f).complexity + N) →
      Ebe1 (V := V) H Be B ε P := by
    intro P hrB hrC hcx
    by_contra h
    have hn1 : ∃ e ∈ H, ∃ Ee : Finset (Pt V), (Be e).IsMeas Ee ∧
        (SigAlg.iInf B (del e)).energy (indicator Ee) + ε ^ 2 ≤
          (SigAlg.iInf P (del e)).energy (indicator Ee) := by
      rw [Ebe1] at h
      push_neg at h
      exact h
    exact hOrInr ⟨P, hrB, hrC, hcx, hn1⟩
  have main : ∀ n, n ≤ N → ∃ P, IsBad (V := V) H Be B ε δ n P := by
    intro n
    induction n with
    | zero =>
        intro _
        have h1 : Ebe1 (V := V) H Be B ε B := by
          intro e he Ee hEe
          have hε2 : 0 < ε ^ 2 := by positivity
          linarith
        have hrB : ∀ f ∈ bdry H, (B f).Refines (B f) := fun f _ => SigAlg.Refines.refl _
        have h2 : ¬ Ebe2 (V := V) H Be δ B := hEbe2' B hrB hB h1
        refine ⟨B, hrB, hB, ?_, h1, h2, ?_⟩
        · intro f hf; omega
        · simp
    | succ n ih =>
        intro hn
        obtain ⟨P, hbad⟩ := ih (Nat.le_of_succ_le hn)
        exact isBad_step hbad hδ hn hEbe1' hEbe2'
  obtain ⟨P, hrefB, hrefC, hcx, h1, h2, henergy⟩ := main N le_rfl
  have hb := energySum_le_of_ebe1 (H := H) (Be := Be) (B := B) (P := P) (m := m) (ε := ε) hm h1
  have hXle : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 / δ ^ 2
      ≤ (Nat.ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 / δ ^ 2) : ℝ) := Nat.le_ceil _
  have hNval : (N : ℝ)
      = (Nat.ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 / δ ^ 2) : ℝ) + 1 := by
    rw [hN, dichBound]
    push_cast
    ring
  have hlt : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 < (N : ℝ) * δ ^ 2 := by
    have h1' : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 / δ ^ 2 < (N : ℝ) := by
      linarith [hXle, hNval]
    rwa [div_lt_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)] at h1'
  linarith

end Szemeredi.Removal
