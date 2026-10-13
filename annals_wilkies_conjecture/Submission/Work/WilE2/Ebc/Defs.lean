/-
  Work.WilE2.Ebc — vocabulary for `Work.WilE2.euclidean_ball_components`.

  The target statement (GV Corollary 3.3 in "Euclidean ball" form, i.e. the *compact variety*
  bound for a Pfaffian variety) will be proved by the Milnor/Petrovskii–Oleinik device as
  presented in Lotz–Natarajan, *Khovanskii's Bézout-type theorem for Pfaffian functions: a
  self-contained proof, and applications*, §"Applications" (a copy of the source lives in
  `Submission/Work/WilE2/.scratch/kh/main.tex`).  The argument, in outline:

  Let `φ := ∑_{f ∈ g} f²` (so `φ ≥ 0` and `φ⁻¹(0) = Z = Zset c g`), let `ρ ≥ 0` and
  `X := Z ∩ B̄_ρ` (the closed Euclidean ball).  For `ε > 0` put

      F_ε(x) := φ(x) + ε (∑ᵢ xᵢ² - ρ²),        D_ε := {x | F_ε x ≤ 0} ⊆ B̄_ρ.

  * Given points `p_1, …, p_N ∈ X` lying in *distinct* components of `X`, the components `Kᵢ^ε`
    of `D_ε` containing `pᵢ` are pairwise distinct for small `ε`
    (`tube_separation`): the sets `Kᵢ^{1/l}` decrease to a compact *connected* set `Aᵢ` contained
    in `X` and containing `pᵢ`, hence `Aᵢ ⊆` the component of `pᵢ`; so `p_j ∉ Aᵢ` for `j ≠ i`.
  * Choosing `ε` with `0` a regular value of `F_ε` (`exists_regular_epsilon`), `X_ε := {F_ε = 0}`
    is a smooth compact hypersurface, and `∅ ≠ ∂Kᵢ^ε ⊆ X_ε`; the component `Γᵢ` of `X_ε` meeting
    `∂Kᵢ^ε` satisfies `Γᵢ ⊆ Kᵢ^ε`, so the `Γᵢ` are pairwise distinct.
  * A linear functional `ℓ_u` (`u ≠ 0`) attains its minimum on the compact `Γᵢ` at a *critical*
    point `zᵢ` of `ℓ_u|_{X_ε}` (`exists_critical_on_regular_level`), i.e. `∇F_ε(zᵢ) ∥ u`.
  * Choosing the direction `u = (1, c)` generically (`exists_generic_slope`, an application of the
    rectangular Sard hypothesis `SardDense`), every solution of the *square* EA system

        F_ε = 0,    ∂_j F_ε - c_j ∂₁ F_ε = 0   (j = 2, …, k)

    with `∂₁F_ε ≠ 0` is non-degenerate.  Each `zᵢ` is such a solution, so `N` is at most the
    number of non-degenerate solutions, which the Khovanskii hypothesis `KhoBound` bounds
    polynomially in the total atom degree.
  * Finally "finite choice": since every finite family of distinct components has at most that
    many members, the set of components of `X` is finite with that cardinality bound, and one
    point per component is a hitting set.

  This module fixes the shared vocabulary: the Euclidean ball, the zero set restricted to the
  ball, the "tube" functions, and the finite-character principle that turns the Khovanskii bound
  on *finite* sets of solutions into a bound on the whole set of solutions.
-/
import Mathlib
import Submission.Work.WilE2.VcbDefs

set_option autoImplicit false
noncomputable section

open Classical
open WilkiesDesign WilkiesDesign.E

namespace Work.WilE2

open scoped Topology

/-- The closed Euclidean ball of radius `ρ` in `ℝᵏ` (written with the sum of squares on purpose:
the canonical norm on `Fin k → ℝ` is the sup norm). -/
def eball (k : ℕ) (ρ : ℝ) : Set (Fin k → ℝ) := {x | ∑ i, (x i) ^ 2 ≤ ρ ^ 2}

@[simp] theorem mem_eball {k : ℕ} {ρ : ℝ} {x : Fin k → ℝ} :
    x ∈ eball k ρ ↔ ∑ i, (x i) ^ 2 ≤ ρ ^ 2 := Iff.rfl

theorem eball_nonneg_radius {k : ℕ} {ρ : ℝ} (h : ρ ≤ 0) : eball k ρ = eball k (-ρ) := by
  unfold eball
  rw [neg_sq]

theorem eball_zero {k : ℕ} : eball k 0 = {0} := by
  unfold eball
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    have h1 : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    have h2 : (x i) ^ 2 = 0 := le_antisymm (le_trans h1 (by simpa using h)) (sq_nonneg _)
    exact sq_eq_zero_iff.mp h2
  · rintro rfl
    simp

theorem isClosed_eball (k : ℕ) (ρ : ℝ) : IsClosed (eball k ρ) := by
  have hcont : Continuous fun x : Fin k → ℝ => ∑ i, (x i) ^ 2 :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2
  have : eball k ρ = (fun x : Fin k → ℝ => ∑ i, (x i) ^ 2) ⁻¹' Set.Iic (ρ ^ 2) := rfl
  rw [this]
  exact isClosed_Iic.preimage hcont

theorem isCompact_eball (k : ℕ) (ρ : ℝ) : IsCompact (eball k ρ) := by
  have hsub : eball k ρ ⊆ Set.pi Set.univ (fun _ : Fin k => Set.Icc (-|ρ|) |ρ|) := by
    intro x hx i _
    have h1 : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    have h2 : (x i) ^ 2 ≤ ρ ^ 2 := le_trans h1 hx
    have h3 : |x i| ≤ |ρ| := by
      calc |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (ρ ^ 2) := Real.sqrt_le_sqrt h2
        _ = |ρ| := Real.sqrt_sq_eq_abs ρ
    exact ⟨neg_le_of_abs_le h3, le_of_abs_le h3⟩
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset (isClosed_eball k ρ) hsub

/-- The zero set of a finite family of EA polynomials on the chain `c`, cut by the closed ball of
radius `ρ`.  This is the set whose components `euclidean_ball_components` has to hit. -/
def Zball {k r : ℕ} (c : EAChain k r) (g : Finset (EAPoly k r)) (ρ : ℝ) : Set (Fin k → ℝ) :=
  Zset c g ∩ eball k ρ

/-- The "tube function" `x ↦ φ x + ε (∑ᵢ xᵢ² - ρ²)` attached to `φ ≥ 0`. -/
def tubeFun {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (ρ ε : ℝ) (x : Fin k → ℝ) : ℝ :=
  φ x + ε * (∑ i, (x i) ^ 2 - ρ ^ 2)

/-- The sublevel set `{x | φ x + ε (∑ᵢ xᵢ² - ρ²) ≤ 0}`. -/
def tubeSet {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (ρ ε : ℝ) : Set (Fin k → ℝ) :=
  {x | tubeFun φ ρ ε x ≤ 0}

/-- The level set `{x | φ x + ε (∑ᵢ xᵢ² - ρ²) = 0}`. -/
def tubeLevel {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (ρ ε : ℝ) : Set (Fin k → ℝ) :=
  {x | tubeFun φ ρ ε x = 0}

/-- **Finite character principle.**  If every finite subset of `S` has at most `M` elements, then
`S` is finite with at most `M` elements.  Used to turn the Khovanskii bound `hE2a`, which is
stated for `Finset`s of solutions, into a bound on the *whole* set of solutions. -/
theorem finite_of_forall_finset_card_le {α : Type*} {S : Set α} {M : ℕ}
    (h : ∀ t : Finset α, (↑t : Set α) ⊆ S → t.card ≤ M) : S.Finite ∧ S.ncard ≤ M := by
  by_cases hfin : S.Finite
  · refine ⟨hfin, ?_⟩
    rw [Set.ncard_eq_toFinset_card S hfin]
    exact h hfin.toFinset (by rw [hfin.coe_toFinset])
  · exfalso
    have hinf : S.Infinite := hfin
    obtain ⟨t, htS, htcard⟩ := hinf.exists_subset_card_eq (M + 1)
    have ht := h t htS
    omega

/-- **Finite character principle, hitting-set form.**  A set all of whose finite subsets have at
most `M` points is covered by a finite set of at most `M` points. -/
theorem exists_finset_cover_of_finset_card_le {α : Type*} {S : Set α} {M : ℕ}
    (h : ∀ t : Finset α, (↑t : Set α) ⊆ S → t.card ≤ M) :
    ∃ t : Finset α, S ⊆ (↑t : Set α) ∧ t.card ≤ M := by
  obtain ⟨hfin, hcard⟩ := finite_of_forall_finset_card_le h
  refine ⟨hfin.toFinset, fun x hx => hfin.mem_toFinset.mpr hx, ?_⟩
  rw [← Set.ncard_eq_toFinset_card S hfin]
  exact hcard

end Work.WilE2
