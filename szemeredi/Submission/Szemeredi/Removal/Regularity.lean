import Mathlib
import Submission.Szemeredi.Removal.Dichotomy

/-!
# The preliminary regularity lemma (Tao, arXiv:math/0503572, Lemma 2.4)

Iterating the dichotomy between structure and pseudorandomness with a growth
function `F` gives a pair of low-order σ-algebras `B_f ⊆ B'_f ⊆ A_f` on the
boundary `∂H` of a hypergraph `H`, such that:

* the coarse algebra `B_f` has complexity at most `max (F m) (max_f #B_f)`;
* the energy of every `B_e`-measurable set increases by less than `ε²` when
  passing from the coarse to the fine approximation;
* the discrepancy of every `B_e`-measurable set with respect to the fine
  approximation is at most `1/F(M)`.

-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

theorem energySum_nonneg (H : Finset (Finset ι)) (Be P : Finset ι → SigAlg (Pt V)) :
    0 ≤ energySum H Be P := by
  classical
  unfold energySum
  refine Finset.sum_nonneg (fun e _ => Finset.sum_nonneg (fun Ee _ => ?_))
  by_cases h : (Be e).IsMeas Ee
  · rw [if_pos h]; exact energy_nonneg _ _
  · rw [if_neg h]

/-- The complexity bound `M = max (F m) (max_f complexity (B f))` attached to a
family of σ-algebras `B` on the boundary. -/
noncomputable def Mbound (F : ℕ → ℕ) (m : ℕ) (H : Finset (Finset ι))
    (Bf : Finset ι → SigAlg (Pt V)) : ℕ :=
  max (F m) ((bdry H).sup (fun f => (Bf f).complexity))

/-- The accuracy `δ = 1/F(M)` used in the preliminary regularity lemma. -/
noncomputable def deltaOf (F : ℕ → ℕ) (m : ℕ) (H : Finset (Finset ι))
    (Bf : Finset ι → SigAlg (Pt V)) : ℝ :=
  1 / (F (Mbound F m H Bf) : ℝ)

/-- The preliminary regularity lemma is satisfied by the family `Bf`. -/
def PrelimDone (H : Finset (Finset ι)) (Be : Finset ι → SigAlg (Pt V)) (F : ℕ → ℕ) (m : ℕ)
    (ε : ℝ) (Bf : Finset ι → SigAlg (Pt V)) : Prop :=
  ∃ Bf' : Finset ι → SigAlg (Pt V),
    (∀ f ∈ bdry H, (Bf f).Refines (Bf' f)) ∧
    (∀ f ∈ bdry H, (Bf' f).Refines (coord (V := V) f)) ∧
    Ebe1 (V := V) H Be Bf ε Bf' ∧
    Ebe2 (V := V) H Be (deltaOf F m H Bf) Bf'

/-- **Preliminary regularity lemma** (Tao, arXiv:math/0503572, Lemma 2.4).  Given
σ-algebras `B_e` on the edges of `H` with `complexity (B_e) ≤ m`, a growth function
`F` (`n + 1 ≤ F n`) and `ε > 0`, there is a family of σ-algebras `B_f ⊆ A_f` on the
boundary such that `B_f` has bounded complexity, the energy of each `B_e`-measurable
set grows by less than `ε²` between the coarse algebra `B_f` and a fine algebra
`B'_f ⊇ B_f`, and the discrepancy of every `B_e`-measurable set with respect to
`B'_f` is at most `1/F(M)` with `M = max (F m) (max_f complexity (B_f))`. -/
theorem preliminary_regularity {H : Finset (Finset ι)} {Be : Finset ι → SigAlg (Pt V)} {m : ℕ}
    {ε : ℝ} {F : ℕ → ℕ}
    (hm : ∀ e ∈ H, (Be e).complexity ≤ m) (hε : 0 < ε) (hF : ∀ n, n + 1 ≤ F n) :
    ∃ Bf : Finset ι → SigAlg (Pt V),
      (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) ∧
      PrelimDone (V := V) H Be F m ε Bf := by
  classical
  set K : ℕ := Nat.ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) / ε ^ 2) + 1 with hK
  by_contra hconcl
  rw [not_exists] at hconcl
  have hdelta_pos : ∀ Bf : Finset ι → SigAlg (Pt V), 0 < deltaOf F m H Bf := by
    intro Bf
    unfold deltaOf
    have h1 : 1 ≤ F (Mbound F m H Bf) := by
      have := hF (Mbound F m H Bf); omega
    have h2 : (0 : ℝ) < (F (Mbound F m H Bf) : ℝ) := by exact_mod_cast h1
    positivity
  have step : ∀ Bf : Finset ι → SigAlg (Pt V),
      (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) →
      ∃ Bf' : Finset ι → SigAlg (Pt V),
        (∀ f ∈ bdry H, (Bf' f).Refines (coord (V := V) f)) ∧
        (∀ f ∈ bdry H, (Bf f).Refines (Bf' f)) ∧
        energySum H Be Bf + ε ^ 2 ≤ energySum H Be Bf' := by
    intro Bf hcoord
    rcases dichotomy (H := H) (Be := Be) (B := Bf) (m := m) hm hcoord hε (hdelta_pos Bf) with
      ⟨Bf', hr, hc, h1, h2⟩ | ⟨Bf', hr, hc, hcx, e, he, Ee, hEe, hjump⟩
    · exact absurd ⟨hcoord, Bf', hr, hc, h1, h2⟩ (hconcl Bf)
    · refine ⟨Bf', hc, hr, ?_⟩
      exact energySum_add_le (H := H) (Be := Be) (P := Bf) (P' := Bf') (e₀ := e) (E₀ := Ee)
        (δ := ε) he hEe (fun e' he' f hf => hr f (mem_bdry.mpr ⟨e', he', hf⟩)) hjump
  have main : ∀ k, k ≤ K → ∃ Bf : Finset ι → SigAlg (Pt V),
      (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) ∧
      energySum H Be (fun _ => SigAlg.triv) + (k : ℝ) * ε ^ 2 ≤ energySum H Be Bf := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨fun _ => SigAlg.triv, ?_, ?_⟩
        · intro f hf x y hy
          simp
        · simp
    | succ k ih =>
        intro hk
        obtain ⟨Bf, hc, hen⟩ := ih (Nat.le_of_succ_le hk)
        obtain ⟨Bf', hc', hstep⟩ := step Bf hc
        exact ⟨Bf', hc', by push_cast; linarith⟩
  obtain ⟨Bf, hc, hen⟩ := main K le_rfl
  have hle := energySum_le (H := H) (Be := Be) (m := m) hm Bf
  have hnon := energySum_nonneg H Be (fun _ => SigAlg.triv)
  have hKl : (K : ℝ) * ε ^ 2 ≤ (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) := by linarith
  have hKge : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) / ε ^ 2 < (K : ℝ) := by
    rw [hK]
    push_cast
    linarith [Nat.le_ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) / ε ^ 2)]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)] at hKge
  exact absurd hKl (not_le.mpr hKge)


theorem triv_complexity : (SigAlg.triv : SigAlg (Pt V)).complexity = 0 := by
  have hsub : Finset.univ.image (fun _ : Pt V => (Finset.univ : Finset (Pt V))) ⊆ {Finset.univ} := by
    intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    simp
  have hcard : (SigAlg.triv : SigAlg (Pt V)).atoms.card ≤ 1 := by
    rw [SigAlg.atoms]
    calc (Finset.univ.image (fun _ : Pt V => (Finset.univ : Finset (Pt V)))).card
        ≤ ({Finset.univ} : Finset (Finset (Pt V))).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  have := SigAlg.complexity_le_of_card_le (P := (SigAlg.triv : SigAlg (Pt V))) (m := 0) (by simpa using hcard)
  omega

theorem dichBound_antitone {H : Finset (Finset ι)} {m : ℕ} {ε δ δ' : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ δ') : dichBound H m ε δ' ≤ dichBound H m ε δ := by
  unfold dichBound
  have hC : 0 ≤ (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 := by positivity
  have h2 : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 / (δ' ^ 2)
      ≤ (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2 / (δ ^ 2) :=
    div_le_div_of_nonneg_left hC (by positivity) (by nlinarith)
  exact Nat.add_le_add_right (Nat.ceil_mono h2) 1

/-- The preliminary regularity lemma is satisfied with discrepancy target `η`. -/
def DoneT (H : Finset (Finset ι)) (Be : Finset ι → SigAlg (Pt V)) (ε η : ℝ)
    (Bf : Finset ι → SigAlg (Pt V)) : Prop :=
  ∃ Bf' : Finset ι → SigAlg (Pt V),
    (∀ f ∈ bdry H, (Bf f).Refines (Bf' f)) ∧
    (∀ f ∈ bdry H, (Bf' f).Refines (coord (V := V) f)) ∧
    Ebe1 (V := V) H Be Bf ε Bf' ∧
    Ebe2 (V := V) H Be η Bf'

/-- Number of iteration steps needed in the target-parameterized preliminary
regularity lemma. -/
noncomputable def prelimK (H : Finset (Finset ι)) (m : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) / ε ^ 2) + 1

/-- Explicit complexity bound of the coarse σ-algebras produced by the
target-parameterized preliminary regularity lemma. -/
noncomputable def prelimBound (H : Finset (Finset ι)) (m : ℕ) (ε η : ℝ) : ℕ :=
  prelimK H m ε * dichBound H m ε η

theorem prelimBound_antitone {H : Finset (Finset ι)} {m : ℕ} {ε : ℝ} {η η' : ℝ}
    (hη : 0 < η) (hη' : η ≤ η') : prelimBound H m ε η' ≤ prelimBound H m ε η := by
  unfold prelimBound
  exact Nat.mul_le_mul_left _ (dichBound_antitone hη hη')

/-- **Preliminary regularity lemma, target form**: with a *fixed* discrepancy
target `η` (rather than `1/F(M)`), the coarse σ-algebras produced by the iteration
have an explicit complexity bound `prelimBound H m ε η`. -/
theorem preliminary_regularity_target {H : Finset (Finset ι)} {Be : Finset ι → SigAlg (Pt V)}
    {m : ℕ} {ε η : ℝ} (hm : ∀ e ∈ H, (Be e).complexity ≤ m) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Bf Bf' : Finset ι → SigAlg (Pt V),
      (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) ∧
      (∀ f ∈ bdry H, (Bf f).Refines (Bf' f)) ∧
      (∀ f ∈ bdry H, (Bf' f).Refines (coord (V := V) f)) ∧
      (∀ f ∈ bdry H, (Bf f).complexity ≤ prelimBound H m ε η) ∧
      Ebe1 (V := V) H Be Bf ε Bf' ∧
      Ebe2 (V := V) H Be η Bf' := by
  classical
  set K : ℕ := prelimK H m ε with hK
  set D : ℕ := dichBound H m ε η with hD
  have hD1 : 1 ≤ D := by rw [hD]; unfold dichBound; omega
  by_contra hconcl
  have hno : ∀ Bf : Finset ι → SigAlg (Pt V),
      (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) →
      (∀ f ∈ bdry H, (Bf f).complexity ≤ prelimBound H m ε η) →
      ¬ DoneT (V := V) H Be ε η Bf := by
    intro Bf h1 h2 h3
    obtain ⟨Bf', hr, hc, h4, h5⟩ := h3
    exact hconcl ⟨Bf, Bf', h1, hr, hc, h2, h4, h5⟩
  have step : ∀ Bf : Finset ι → SigAlg (Pt V),
      (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) →
      ∀ C : ℕ, (∀ f ∈ bdry H, (Bf f).complexity ≤ C) →
      C + D ≤ prelimBound H m ε η → ¬ DoneT (V := V) H Be ε η Bf →
      ∃ Bf' : Finset ι → SigAlg (Pt V),
        (∀ f ∈ bdry H, (Bf' f).Refines (coord (V := V) f)) ∧
        (∀ f ∈ bdry H, (Bf f).Refines (Bf' f)) ∧
        (∀ f ∈ bdry H, (Bf' f).complexity ≤ C + D) ∧
        energySum H Be Bf + ε ^ 2 ≤ energySum H Be Bf' := by
    intro Bf hcoord C hC hCle hnotDone
    rcases dichotomy (H := H) (Be := Be) (B := Bf) (m := m) hm hcoord hε hη with
      ⟨Bf', hr, hc, h1, h2⟩ | ⟨Bf', hr, hc, hcx, e, he, Ee, hEe, hjump⟩
    · exact absurd ⟨Bf', hr, hc, h1, h2⟩ hnotDone
    · refine ⟨Bf', hc, hr, ?_, ?_⟩
      · intro f hf
        have := hcx f hf
        have := hC f hf
        omega
      · exact energySum_add_le (H := H) (Be := Be) (P := Bf) (P' := Bf') (e₀ := e) (E₀ := Ee)
          (δ := ε) he hEe (fun e' he' f hf => hr f (mem_bdry.mpr ⟨e', he', hf⟩)) hjump
  have main : ∀ k, k ≤ K → ∃ Bf : Finset ι → SigAlg (Pt V),
      (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) ∧
      (∀ f ∈ bdry H, (Bf f).complexity ≤ k * D) ∧
      (DoneT (V := V) H Be ε η Bf ∨
        energySum H Be (fun _ => SigAlg.triv) + (k : ℝ) * ε ^ 2 ≤ energySum H Be Bf) := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨fun _ => SigAlg.triv, ?_, ?_, Or.inr ?_⟩
        · intro f hf x y hy; simp
        · intro f hf
          rw [Nat.zero_mul, triv_complexity]
        · simp
    | succ k ih =>
        intro hk
        obtain ⟨Bf, hc, hcx, hcase⟩ := ih (Nat.le_of_succ_le hk)
        by_cases hdone : DoneT (V := V) H Be ε η Bf
        · refine ⟨Bf, hc, fun f hf => ?_, Or.inl hdone⟩
          have := hcx f hf
          have : (k + 1) * D = k * D + D := by ring
          omega
        · have henergy : energySum H Be (fun _ => SigAlg.triv) + (k : ℝ) * ε ^ 2
              ≤ energySum H Be Bf := hcase.resolve_left hdone
          have hkK : k ≤ K := le_trans (Nat.le_succ k) hk
          have hle : k * D + D ≤ prelimBound H m ε η := by
            have h1 : k * D + D = (k + 1) * D := by ring
            rw [h1]
            exact Nat.mul_le_mul_right D hk
          obtain ⟨Bf', hc', hr, hcx', hstep⟩ := step Bf hc (k * D) hcx hle hdone
          refine ⟨Bf', hc', fun f hf => ?_, Or.inr ?_⟩
          · have := hcx' f hf
            have : (k + 1) * D = k * D + D := by ring
            omega
          · push_cast
            linarith
  obtain ⟨Bf, hc, hcx, hcase⟩ := main K le_rfl
  rcases hcase with hdone | henergy
  · exact hno Bf hc hcx hdone
  · have hle := energySum_le (H := H) (Be := Be) (m := m) hm Bf
    have hnon := energySum_nonneg H Be (fun _ => SigAlg.triv)
    have hKl : (K : ℝ) * ε ^ 2 ≤ (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) := by linarith
    have hKge : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) / ε ^ 2 < (K : ℝ) := by
      rw [hK, prelimK]
      push_cast
      linarith [Nat.le_ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) / ε ^ 2)]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)] at hKge
    exact absurd hKl (not_le.mpr hKge)


/-- The explicit complexity ladder for the `δ = 1/F(M)`-form preliminary regularity
lemma: at each iteration the complexity grows by at most one dichotomy increment
`dichBound`, evaluated at the current a priori bound. -/
noncomputable def ladder (H : Finset (Finset ι)) (m : ℕ) (ε : ℝ) (G : ℕ → ℕ) : ℕ → ℕ :=
  Nat.rec (G m) (fun _ M => M + dichBound H m ε (1 / (G M : ℝ)))

@[simp] theorem ladder_zero (H : Finset (Finset ι)) (m : ℕ) (ε : ℝ) (G : ℕ → ℕ) :
    ladder H m ε G 0 = G m := rfl

@[simp] theorem ladder_succ (H : Finset (Finset ι)) (m : ℕ) (ε : ℝ) (G : ℕ → ℕ) (k : ℕ) :
    ladder H m ε G (k + 1) = ladder H m ε G k + dichBound H m ε (1 / (G (ladder H m ε G k) : ℝ)) :=
  rfl

theorem ladder_mono (H : Finset (Finset ι)) (m : ℕ) (ε : ℝ) (G : ℕ → ℕ) :
    Monotone (ladder H m ε G) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [ladder_succ]
  exact Nat.le_add_right _ _

theorem le_ladder (H : Finset (Finset ι)) (m : ℕ) (ε : ℝ) (G : ℕ → ℕ) (k : ℕ) :
    G m ≤ ladder H m ε G k :=
  le_trans (le_of_eq (ladder_zero H m ε G).symm) (ladder_mono H m ε G (Nat.zero_le k))

/-- The preliminary regularity goal together with a *declared* complexity bound. -/
def PrelimDoneB (H : Finset (Finset ι)) (Be : Finset ι → SigAlg (Pt V)) (G : ℕ → ℕ) (m : ℕ)
    (ε : ℝ) (B : ℕ) (Bf : Finset ι → SigAlg (Pt V)) : Prop :=
  (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) ∧
  (∀ f ∈ bdry H, (Bf f).complexity ≤ B) ∧
  PrelimDone (V := V) H Be G m ε Bf

/-- **Bounded preliminary regularity lemma** (Tao Lemma 2.4, `δ = 1/F(M)` form) with
the explicit complexity bound `ladder H m ε G (prelimK H m ε)`. -/
theorem preliminary_regularity_bounded {H : Finset (Finset ι)} {Be : Finset ι → SigAlg (Pt V)}
    {m : ℕ} {ε : ℝ} {G : ℕ → ℕ}
    (hm : ∀ e ∈ H, (Be e).complexity ≤ m) (hε : 0 < ε)
    (hG : ∀ n, n + 1 ≤ G n) (hGmono : Monotone G)
    {B : ℕ} (hB : ladder H m ε G (prelimK H m ε) ≤ B) :
    ∃ Bf, PrelimDoneB (V := V) H Be G m ε B Bf := by
  classical
  set K : ℕ := prelimK H m ε with hK
  have hGK : ∀ k ≤ K, G m ≤ ladder H m ε G k := fun k _ => le_ladder H m ε G k
  by_contra hconcl
  have hno : ∀ Bf, (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) →
      (∀ f ∈ bdry H, (Bf f).complexity ≤ B) →
      ¬ PrelimDone (V := V) H Be G m ε Bf := by
    intro Bf h1 h2 h3
    exact hconcl ⟨Bf, h1, h2, h3⟩
  have step : ∀ Bf C, (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) →
      (∀ f ∈ bdry H, (Bf f).complexity ≤ C) → G m ≤ C → C ≤ B →
      ¬ PrelimDone (V := V) H Be G m ε Bf →
      ∃ Bf', (∀ f ∈ bdry H, (Bf' f).Refines (coord (V := V) f)) ∧
        (∀ f ∈ bdry H, (Bf f).Refines (Bf' f)) ∧
        (∀ f ∈ bdry H, (Bf' f).complexity
          ≤ C + dichBound H m ε (1 / (G C : ℝ))) ∧
        energySum H Be Bf + ε ^ 2 ≤ energySum H Be Bf' := by
    intro Bf C hcoord hC hGC hCB hnotDone
    have hMboundC : Mbound G m H Bf ≤ C := by
      unfold Mbound
      exact max_le hGC (Finset.sup_le (fun f hf => hC f hf))
    have hδpos : 0 < deltaOf G m H Bf := by
      unfold deltaOf
      have h1 : 1 ≤ G (Mbound G m H Bf) := by have := hG (Mbound G m H Bf); omega
      have h2 : (0 : ℝ) < (G (Mbound G m H Bf) : ℝ) := by exact_mod_cast h1
      positivity
    have hGCM : (G (Mbound G m H Bf) : ℝ) ≤ (G C : ℝ) := by
      exact_mod_cast hGmono hMboundC
    have hCpos : (0 : ℝ) < (G C : ℝ) := by
      have h1 : 1 ≤ G C := by have := hG C; omega
      exact_mod_cast h1
    have hMbpos : (0 : ℝ) < (G (Mbound G m H Bf) : ℝ) := by
      have h1 : 1 ≤ G (Mbound G m H Bf) := by have := hG (Mbound G m H Bf); omega
      exact_mod_cast h1
    have hd : 1 / (G C : ℝ) ≤ deltaOf G m H Bf := by
      unfold deltaOf
      exact div_le_div_of_nonneg_left (by norm_num) hMbpos hGCM
    rcases dichotomy (H := H) (Be := Be) (B := Bf) (m := m) hm hcoord hε hδpos with
      ⟨Bf', hr, hc, h1, h2⟩ | ⟨Bf', hr, hc, hcx, e, he, Ee, hEe, hjump⟩
    · exact absurd ⟨Bf', hr, hc, h1, h2⟩ hnotDone
    · refine ⟨Bf', hc, hr, fun f hf => ?_, ?_⟩
      · have h1 := hcx f hf
        have h2 := hC f hf
        have h3 : dichBound H m ε (deltaOf G m H Bf) ≤ dichBound H m ε (1 / (G C : ℝ)) :=
          dichBound_antitone (by positivity) hd
        omega
      · exact energySum_add_le (H := H) (Be := Be) (P := Bf) (P' := Bf') (e₀ := e) (E₀ := Ee)
          (δ := ε) he hEe (fun e' he' f hf => hr f (mem_bdry.mpr ⟨e', he', hf⟩)) hjump
  have main : ∀ k, k ≤ K → ∃ Bf, (∀ f ∈ bdry H, (Bf f).Refines (coord (V := V) f)) ∧
      (∀ f ∈ bdry H, (Bf f).complexity ≤ ladder H m ε G k) ∧
      (PrelimDone (V := V) H Be G m ε Bf ∨
        energySum H Be (fun _ => SigAlg.triv) + (k : ℝ) * ε ^ 2 ≤ energySum H Be Bf) := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨fun _ => SigAlg.triv, ?_, ?_, Or.inr ?_⟩
        · intro f hf x y hy; simp
        · intro f hf
          rw [triv_complexity]; exact Nat.zero_le _
        · simp
    | succ k ih =>
        intro hk
        obtain ⟨Bf, hc, hcx, hcase⟩ := ih (Nat.le_of_succ_le hk)
        by_cases hdone : PrelimDone (V := V) H Be G m ε Bf
        · refine ⟨Bf, hc, fun f hf => ?_, Or.inl hdone⟩
          have := hcx f hf
          have h1 : ladder H m ε G k ≤ ladder H m ε G (k + 1) := by
            rw [ladder_succ]; exact Nat.le_add_right _ _
          omega
        · have henergy : energySum H Be (fun _ => SigAlg.triv) + (k : ℝ) * ε ^ 2
              ≤ energySum H Be Bf := hcase.resolve_left hdone
          have hkB : ladder H m ε G (k + 1) ≤ B := by
            refine le_trans (ladder_mono H m ε G hk) hB
          obtain ⟨Bf', hc', hr, hcx', hstep⟩ := step Bf (ladder H m ε G k) hc hcx
            (hGK k (by omega)) (le_trans (ladder_mono H m ε G (by omega : k ≤ K)) hB) hdone
          refine ⟨Bf', hc', fun f hf => ?_, Or.inr ?_⟩
          · have h1 := hcx' f hf
            rw [ladder_succ]; exact h1
          · push_cast
            linarith
  obtain ⟨Bf, hc, hcx, hcase⟩ := main K le_rfl
  rcases hcase with hdone | henergy
  · exact hno Bf hc (fun f hf => le_trans (hcx f hf) hB) hdone
  · have hle := energySum_le (H := H) (Be := Be) (m := m) hm Bf
    have hnon := energySum_nonneg H Be (fun _ => SigAlg.triv)
    have hKl : (K : ℝ) * ε ^ 2 ≤ (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) := by linarith
    have hKge : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) / ε ^ 2 < (K : ℝ) := by
      rw [hK, prelimK]
      push_cast
      linarith [Nat.le_ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) / ε ^ 2)]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)] at hKge
    exact absurd hKl (not_le.mpr hKge)

end Szemeredi.Removal
