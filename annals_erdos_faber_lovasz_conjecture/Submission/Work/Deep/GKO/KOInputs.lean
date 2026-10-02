import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.KOReduction
import Submission.Work.Deep.GKO.KOAssembly
import Submission.Work.Deep.GKO.Combine

/-!
# Kühn–Osthus' two tools, and the verified assembly

`Work.Deep.GKO.KOStatement` is Theorem 1.2 of Kühn–Osthus, *Hamilton decompositions of regular
expanders* (arXiv:1202.6219 / JCTB 104 (2014)).  Their proof (§2.1 of that paper) rests on
exactly two tools:

* `ApproxHamDecompStatement` — an **approximate Hamilton decomposition** (their Theorem 1.3, due
  to Osthus–Staden): a regular robust expander of linear degree splits into a
  Hamilton-decomposable part plus a `≤ ηr`-regular leftover, for every `η > 0`;
* `AbsorptionStatement` — the **robust decomposition lemma** (their Lemma 11.2, in the informal
  form stated in §2.1): every regular robust expander contains a spanning subgraph `H` of degree
  `≤ γn` which is *`γ`-robustly decomposable*, meaning that `H ⊔ H₀` has a Hamilton
  decomposition for every regular `H₀` of degree `≤ γn` that is edge-disjoint from `H`.

This module states both, and proves (`koStatement_of_approx_and_absorption`) that together they
imply `KOStatement`.  The assembly is the paper's own argument: delete the absorbed `H`, apply
the approximate decomposition to the remainder (which is still a robust expander by
`robustExpander_sdiff`, with `ν` halved and degree `≥ αn/2` — exactly the paper's check), and
recombine the Hamilton decompositions of `H ⊔ H₀` and of the found cycles.

Neither input is proved here: they are the two deep theorems of the Kühn–Osthus line.  But with
this reduction, `KOStatement` (and hence, through
`Work.Deep.GKO.gkoStatementTau_of_KOExplicit`, Theorem 10.8) is *exactly* those two statements,
and every other ingredient — the deletion bookkeeping, the degree arithmetic, the combination of
Hamilton decompositions — is verified.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Elementary API -/

/-- A Hamilton cycle is its own Hamilton decomposition. -/
theorem hasHamiltonDecomposition_of_isHamiltonCycle' {G : SimpleGraph (Fin n)}
    (h : IsHamiltonCycle' G) : HasHamiltonDecomposition G :=
  ⟨1, fun _ => G, fun _ => le_rfl, fun _ => h,
    fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ he => ⟨0, he⟩⟩

/-- Hamilton decompositions of edge-disjoint subgraphs combine. -/
theorem hasHamiltonDecomposition_sup {A B : SimpleGraph (Fin n)}
    (hA : HasHamiltonDecomposition A) (hB : HasHamiltonDecomposition B)
    (hd : Disjoint A.edgeSet B.edgeSet) : HasHamiltonDecomposition (A ⊔ B) := by
  classical
  obtain ⟨k₁, C₁, hle₁, hcyc₁, hdisj₁, hcov₁⟩ := hA
  obtain ⟨k₂, C₂, hle₂, hcyc₂, hdisj₂, hcov₂⟩ := hB
  refine ⟨k₁ + k₂,
    fun i => if h : i.val < k₁ then C₁ ⟨i.val, h⟩ else C₂ ⟨i.val - k₁, by omega⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i.val < k₁
    · simp only [dif_pos h]
      exact le_trans (hle₁ ⟨i.val, h⟩) le_sup_left
    · simp only [dif_neg h]
      exact le_trans (hle₂ ⟨i.val - k₁, by omega⟩) le_sup_right
  · intro i
    by_cases h : i.val < k₁
    · simp only [dif_pos h]; exact hcyc₁ _
    · simp only [dif_neg h]; exact hcyc₂ _
  · intro i j hij
    by_cases hi : i.val < k₁ <;> by_cases hj : j.val < k₁
    · simp only [dif_pos hi, dif_pos hj]
      exact hdisj₁ _ _ (fun hc => hij (by
        apply Fin.ext
        have hv := congrArg Fin.val hc
        simpa using hv))
    · simp only [dif_pos hi, dif_neg hj]
      exact Disjoint.mono (SimpleGraph.edgeSet_mono (hle₁ ⟨i.val, hi⟩))
        (SimpleGraph.edgeSet_mono (hle₂ ⟨j.val - k₁, by omega⟩)) hd
    · simp only [dif_neg hi, dif_pos hj]
      exact Disjoint.mono (SimpleGraph.edgeSet_mono (hle₂ ⟨i.val - k₁, by omega⟩))
        (SimpleGraph.edgeSet_mono (hle₁ ⟨j.val, hj⟩)) hd.symm
    · simp only [dif_neg hi, dif_neg hj]
      exact hdisj₂ _ _ (fun hc => hij (Fin.ext (by
        have hv := congrArg Fin.val hc
        simp only [Fin.val_mk] at hv
        omega)))
  · intro e he
    rw [SimpleGraph.edgeSet_sup, Set.mem_union] at he
    rcases he with he | he
    · obtain ⟨i, hi⟩ := hcov₁ e he
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      simp only [dif_pos i.isLt]
      exact hi
    · obtain ⟨i, hi⟩ := hcov₂ e he
      refine ⟨⟨i.val + k₁, by omega⟩, ?_⟩
      simp only [dif_neg (by omega : ¬ i.val + k₁ < k₁)]
      have hcast : (⟨i.val + k₁ - k₁, by omega⟩ : Fin k₂) = i := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      rw [hcast]
      exact hi

/-- Splitting off a subgraph. -/
theorem sup_sdiff_of_le {G H : SimpleGraph (Fin n)} (h : H ≤ G) : H ⊔ (G \ H) = G := by
  ext u v
  rw [SimpleGraph.sup_adj]
  constructor
  · rintro (huv | huv)
    · exact h huv
    · exact (SimpleGraph.sdiff_adj G H u v).mp huv |>.1
  · intro huv
    by_cases hh : H.Adj u v
    · exact Or.inl hh
    · exact Or.inr ⟨huv, hh⟩

/-- A subgraph of `G \ H` is edge-disjoint from `H`. -/
theorem disjoint_of_le_sdiff {G H H₀ : SimpleGraph (Fin n)} (h : H₀ ≤ G \ H) :
    Disjoint H.edgeSet H₀.edgeSet := by
  rw [Set.disjoint_left]
  intro e heH heH₀
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet] at heH heH₀
    exact (SimpleGraph.sdiff_adj G H u v).mp (h heH₀) |>.2 heH

/-- A regular graph's degree is at most the number of vertices (when there is a vertex). -/
theorem IsRegularOf.le_card {G : SimpleGraph (Fin n)} {r : ℕ} (h : IsRegularOf G r) (hn : 0 < n) :
    r ≤ n := by
  have h1 : Nat.card (G.neighborSet (⟨0, hn⟩ : Fin n)) ≤ Nat.card (Fin n) := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_univ (α := Fin n)]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  rw [h ⟨0, hn⟩, Nat.card_fin] at h1
  exact h1

/-- The empty graph has a (trivial) Hamilton decomposition. -/
theorem hasHamiltonDecomposition_bot (n : ℕ) :
    HasHamiltonDecomposition (⊥ : SimpleGraph (Fin n)) :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun e he => by simp at he⟩

/-! ## The two tools -/

/-- **Robustly decomposable**: adding any regular spanning subgraph of degree at most
`γ n`, edge-disjoint from `H`, leaves a Hamilton-decomposable graph (the paper's notion in
§2.1). -/
def RobustlyDecomposable (H : SimpleGraph (Fin n)) (γ : ℝ) : Prop :=
  ∀ H₀ : SimpleGraph (Fin n), (∃ d : ℕ, IsRegularOf H₀ d ∧ (d : ℝ) ≤ γ * (n : ℝ)) →
    Disjoint H.edgeSet H₀.edgeSet → HasHamiltonDecomposition (H ⊔ H₀)

/-- **Approximate Hamilton decomposition** (Kühn–Osthus, Theorem 1.3, after Osthus–Staden):
a regular robust expander of linear degree splits into a Hamilton-decomposable part and a
`≤ ηr`-regular leftover. -/
def ApproxHamDecompStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧ ∀ ν η : ℝ, 0 < ν → 0 < η → ν ≤ τ → ∃ n₀ : ℕ,
    ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), RobustExpander G ν τ → ∀ r : ℕ, IsRegularOf G r →
      α * (n : ℝ) ≤ (r : ℝ) → ∃ (G₁ H₀ : SimpleGraph (Fin n)) (d : ℕ),
        G₁ ≤ G ∧ H₀ ≤ G ∧ Disjoint G₁.edgeSet H₀.edgeSet ∧ G₁ ⊔ H₀ = G ∧
        HasHamiltonDecomposition G₁ ∧ IsRegularOf H₀ d ∧ (d : ℝ) ≤ η * (r : ℝ)

/-- **The robust decomposition lemma** (Kühn–Osthus, Lemma 11.2, in the informal form of
§2.1): every regular robust expander contains a `γn`-sparse spanning subgraph which is
`γ`-robustly decomposable, with `γ` as small as desired relative to `ν`. -/
def AbsorptionStatement : Prop :=
  ∀ α : ℝ, 0 < α → ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ ν / 2 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      RobustExpander G ν τ → ∀ r : ℕ, IsRegularOf G r → α * (n : ℝ) ≤ (r : ℝ) →
        ∃ (H : SimpleGraph (Fin n)) (d : ℕ), H ≤ G ∧ IsRegularOf H d ∧
          (d : ℝ) ≤ γ * (n : ℝ) ∧ RobustlyDecomposable H γ

/-! ## The assembly: the two tools imply `KOStatement` -/

/-- **Kühn–Osthus' Theorem 1.2 follows from its two tools.** -/
theorem koStatement_of_approx_and_absorption (hApp : ApproxHamDecompStatement)
    (hAbs : AbsorptionStatement) : KOStatement := by
  intro α hα
  obtain ⟨τ_a, hτ_a, hAbs'⟩ := hAbs α hα
  obtain ⟨τ_b, hτ_b, hApp'⟩ := hApp (α / 2) (by linarith)
  refine ⟨min τ_a (min τ_b α), lt_min hτ_a (lt_min hτ_b hα), ?_⟩
  intro ν hν hντ
  have hντa : ν ≤ τ_a := le_trans hντ (min_le_left _ _)
  have hντb : ν ≤ τ_b := le_trans hντ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hνα : ν ≤ α := le_trans hντ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨γ, hγ0, hγν, n₀a, hAa⟩ := hAbs' ν hν hντa
  obtain ⟨n₀b, hApp''⟩ := hApp' (ν / 2) (γ / 2) (by linarith) (by linarith) (by linarith)
  refine ⟨max n₀a n₀b, ?_⟩
  intro n hn G hG r hr hrn _
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    haveI : Subsingleton (SimpleGraph (Fin 0)) :=
      ⟨fun G G' => by ext u; exact u.elim0⟩
    rw [Subsingleton.elim G ⊥]
    exact hasHamiltonDecomposition_bot 0
  have hn1 : n ≥ n₀a := le_trans (le_max_left _ _) hn
  have hn2 : n ≥ n₀b := le_trans (le_max_right _ _) hn
  -- the absorbed subgraph
  have hGτa : RobustExpander G ν τ_a := robustExpander_mono_tau (min_le_left _ _) hG
  have hGτb : RobustExpander G ν τ_b :=
    robustExpander_mono_tau (le_trans (min_le_right _ _) (min_le_left _ _)) hG
  obtain ⟨H, d, hHG, hHreg, hHd, hHdec⟩ := hAa n hn1 G hGτa r hr hrn
  -- the remainder is still a regular robust expander
  have hdd : (d : ℝ) ≤ ν / 2 * (n : ℝ) := by nlinarith
  have hdα : (d : ℝ) ≤ α / 2 * (n : ℝ) := by nlinarith
  have hdr : (d : ℝ) ≤ (r : ℝ) := by nlinarith
  have hdrNat : d ≤ r := by exact_mod_cast hdr
  have hreg' : IsRegularOf (G \ H) (r - d) := isRegularOf_sdiff hHG hr hHreg
  have hrob' : RobustExpander (G \ H) (ν / 2) τ_b :=
    robustExpander_sdiff hν hGτb hHreg hdd
  have hdeg' : α / 2 * (n : ℝ) ≤ ((r - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdrNat]
    nlinarith
  -- approximate decomposition of the remainder
  obtain ⟨G₁, H₀, d₀, hG₁le, hH₀le, hdisj₁, hsplit, hdec₁, hH₀reg, hH₀d⟩ :=
    hApp'' n hn2 (G \ H) hrob' (r - d) hreg' hdeg'
  -- the leftover is absorbed by `H`
  have hrn : r ≤ n := IsRegularOf.le_card hr hnpos
  have hH₀small : (d₀ : ℝ) ≤ γ * (n : ℝ) := by
    have h : ((r - d : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [Nat.cast_sub hdrNat]
      have : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
      linarith
    nlinarith
  have hdisjHH₀ : Disjoint H.edgeSet H₀.edgeSet := disjoint_of_le_sdiff hH₀le
  have hdecHH₀ : HasHamiltonDecomposition (H ⊔ H₀) :=
    hHdec H₀ ⟨d₀, hH₀reg, hH₀small⟩ hdisjHH₀
  -- recombine
  have hdisj' : Disjoint (H ⊔ H₀).edgeSet G₁.edgeSet := by
    rw [SimpleGraph.edgeSet_sup, Set.disjoint_union_left]
    refine ⟨?_, ?_⟩
    · -- `H` is disjoint from `G₁ ≤ G \ H`
      exact Disjoint.mono (le_rfl : H.edgeSet ⊆ H.edgeSet) (SimpleGraph.edgeSet_mono hG₁le)
        (disjoint_of_le_sdiff (le_refl (G \ H)))
    · exact hdisj₁.symm
  have hfinal : G = (H ⊔ H₀) ⊔ G₁ := by
    rw [← sup_sdiff_of_le hHG, ← hsplit]
    ac_rfl
  rw [hfinal]
  exact hasHamiltonDecomposition_sup hdecHH₀ hdec₁ hdisj'

end

end Work.Deep.GKO
