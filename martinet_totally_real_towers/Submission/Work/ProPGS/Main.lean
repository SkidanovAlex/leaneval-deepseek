import Submission.Work.ProPGS.Defs

/-!
# `Work.ProPGS.Main` -- the headline theorems

**Namespace** `Work.ProPGS`; module `Submission.Work.ProPGS.Main`.

The endgame forms, derived from the single input `Work.ProPGS.ProPGolodShafarevich`.  Each theorem
below therefore carries that hypothesis; the unconditional versions (with
`Work.ProPGS.ProPGolodShafarevich` proved) are in `Submission/Work/ProPGS/Unconditional.lean`.

## Consumer contract

For `Q` a finite `2`-group with a minimal generating family `gen : Fin 5 → Q` and
`Nat.card (Work.RelatorRank.contH2 Q) ≤ 64` (`= dim_{𝔽₂} H²(Q,𝔽₂) ≤ 6`):

* `Work.ProPGS.subsingleton_of_card_contH2_le_sixtyfour_of_proPGolodShafarevich` -- `False`;
* `Work.ProPGS.subsingleton_of_contH2_le_sixtyfour_of_proPGolodShafarevich` -- `Subsingleton Q`.

Both need `[DiscreteTopology Q]`, which holds for `Q := K ≃ₐ[ℚ] K` a finite Galois group.  The
topology-free shape is `Work.ProPGS.false_of_h2DimOf_le_five_of_proPGolodShafarevich`, and the compact totally disconnected
shape is `Work.ProPGS.infinite_of_dense_five_contH2_le_six_of_proPGolodShafarevich`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.ProPGS

open Work.HopfGaschutz

/-- **The finite `p`-group endgame, in the presentation (`h2DimOf`) language.**  A nontrivial finite
`p`-group with a minimal generating family of size five and `dim_{𝔽_p} H² ≤ r` with `4r ≤ 25` does
not exist.  (`r = 6` is the case of the deliverable.) -/
theorem false_of_h2DimOf_le_five_of_proPGolodShafarevich {p : ℕ} (h : ProPGolodShafarevich p)
    {Q : Type} [Group Q] [Fintype Q] [Nontrivial Q] (hQ : IsPGroup p Q)
    (gen : Fin 5 → Q) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → 5 ≤ S.card)
    {r : ℕ} (hr : 4 * r ≤ 25) (h2 : h2DimOf p (Fin 5) Q gen ≤ r) : False := by
  have hmin' : IsMinimalGeneratingFamily gen :=
    ⟨hgen, fun S hS => by simpa using hmin S hS⟩
  have hgs := h (Fin 5) Q hQ gen hmin'
  have h5 : Fintype.card (Fin 5) ^ 2 = (25 : ℕ) := by simp
  omega

/-- `Work.ProPGS.false_of_h2DimOf_le_five_of_proPGolodShafarevich` at `r = 6`. -/
theorem subsingleton_of_h2DimOf_le_six_of_proPGolodShafarevich {p : ℕ} (h : ProPGolodShafarevich p)
    {Q : Type} [Group Q] [Fintype Q] [Nontrivial Q] (hQ : IsPGroup p Q)
    (gen : Fin 5 → Q) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → 5 ≤ S.card)
    (h2 : h2DimOf p (Fin 5) Q gen ≤ 6) : False :=
  false_of_h2DimOf_le_five_of_proPGolodShafarevich h hQ gen hgen hmin (by norm_num) h2

/-- **The finite `2`-group endgame, in the cohomological language.**  A nontrivial finite `2`-group
with a minimal generating family of size five and at most `64` elements in `H²(·,𝔽₂)` does not
exist: `dim_{𝔽₂} H²(Q,𝔽₂) ≤ 6`, while Golod--Shafarevich forces `dim_{𝔽₂} H²(Q,𝔽₂) ≥ 7`. -/
theorem subsingleton_of_contH2_le_sixtyfour_of_proPGolodShafarevich (h : ProPGolodShafarevich 2)
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    [Fintype Q] [Nontrivial Q] (hQ : IsPGroup 2 Q) (gen : Fin 5 → Q)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → 5 ≤ S.card)
    (h2 : Nat.card (Work.RelatorRank.contH2 Q) ≤ 64) : Subsingleton Q := by
  letI : TopologicalSpace (FreeGroup (Fin 5)) := ⊥
  haveI : DiscreteTopology (FreeGroup (Fin 5)) := ⟨rfl⟩
  have hmin' : IsMinimalGeneratingFamily gen :=
    ⟨hgen, fun S hS => by simpa using hmin S hS⟩
  have hgs := h (Fin 5) Q hQ gen hmin'
  have h5 : Fintype.card (Fin 5) ^ 2 = (25 : ℕ) := by simp
  have hge : 7 ≤ h2DimOf 2 (Fin 5) Q gen := by omega
  have hbr := h2DimOf_eq_log_card_contH2 gen hgen
    (le_relFrattini_of_minimal_generating hQ gen hgen hmin)
  have hlog : 7 ≤ Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Q)) := by omega
  have hmono : Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Q)) ≤ Nat.log 2 64 :=
    Nat.log_mono_right h2
  have h64 : Nat.log 2 64 = 6 := by decide
  omega

/-- **THE PRIMARY TARGET.**  No nontrivial finite `2`-group has a minimal generating family of size
five together with `Nat.card (H²(Q,𝔽₂)) ≤ 64`.

This is the statement `fundmath3-martinet_totally_real_towers` asked for, in the requested shape.
It is proved from the pro-`p` Golod--Shafarevich inequality, which is *not* the (open) efficiency
statement for finite `p`-groups: see `Work.ProPGS.gaschutzDictionary_implies_proPGolodShafarevich`
and `Work.HopfGaschutz.gaschutzDictionary_iff_minimalRelatorSet`. -/
theorem subsingleton_of_card_contH2_le_sixtyfour_of_proPGolodShafarevich (h : ProPGolodShafarevich 2) :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
      [Fintype Q] [Nontrivial Q], IsPGroup 2 Q →
      (gen : Fin 5 → Q) → Subgroup.closure (Set.range gen) = ⊤ →
      (∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → 5 ≤ S.card) →
      Nat.card (Work.RelatorRank.contH2 Q) ≤ 64 → False := by
  intro Q _ _ _ _ _ _ hQ gen hgen hmin h2
  exact not_subsingleton Q (subsingleton_of_contH2_le_sixtyfour_of_proPGolodShafarevich h hQ gen hgen hmin h2)

/-- **The general pro-`p` Golod--Shafarevich inequality** in the form of the deliverable: for a
finite `p`-group with a minimal generating family `gen : α → Q`,

  `4 · dim_{𝔽_p} H²(Q,𝔽_p) > (d(Q))²`,

with `d(Q) = Fintype.card α` and `dim_{𝔽_p} H²(Q,𝔽_p) = h2DimOf p α Q gen`. -/
theorem four_mul_dim_contH2_lt_card_sq_of_proPGolodShafarevich {p : ℕ} (h : ProPGolodShafarevich p)
    {α : Type} [Fintype α] {Q : Type} [Group Q] [Fintype Q] [Nontrivial Q]
    (hQ : IsPGroup p Q) (gen : α → Q) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → Fintype.card α ≤ S.card) :
    4 * h2DimOf p α Q gen > Fintype.card α ^ 2 :=
  h α Q hQ gen ⟨hgen, hmin⟩

/-- The same, with the `𝔽₂`-dimension of the genuine cohomology group `H²(Q,𝔽₂)`. -/
theorem four_mul_log_card_contH2_lt_card_sq_of_proPGolodShafarevich (h : ProPGolodShafarevich 2)
    {α : Type} [Fintype α] [DecidableEq α] {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [DiscreteTopology Q] [TopologicalSpace (FreeGroup α)] [DiscreteTopology (FreeGroup α)]
    [Fintype Q] [Nontrivial Q] (hQ : IsPGroup 2 Q) (gen : α → Q)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → Fintype.card α ≤ S.card) :
    4 * Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Q)) > Fintype.card α ^ 2 := by
  have heq := h2DimOf_eq_log_card_contH2 gen hgen
    (le_relFrattini_of_minimal_generating hQ gen hgen hmin)
  have hmain := four_mul_dim_contH2_lt_card_sq_of_proPGolodShafarevich h hQ gen hgen hmin
  omega

/-- **The topological (pro-`2`) form of the criterion.**  A compact, Hausdorff, totally disconnected
group `Γ` which

* is pro-`2` (every finite continuous quotient is a `2`-group),
* has a dense generating family `gen : Fin 5 → Γ` which cannot be thinned to four elements, and
* satisfies `Nat.card H²(Γ,𝔽₂) ≤ 64`

is **infinite**.  For `Γ = K ≃ₐ[ℚ] K` the maximal tame pro-`2` extension of `ℚ` all three
hypotheses are supplied by the arithmetic input and by `Work.TameArithmetic`. -/
theorem infinite_of_dense_five_contH2_le_six_of_proPGolodShafarevich (h : ProPGolodShafarevich 2)
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Nontrivial Γ]
    (hpro : ∀ (N : Subgroup Γ) [N.Normal], IsOpen (N : Set Γ) → IsPGroup 2 (Γ ⧸ N))
    (gen : Fin 5 → Γ) (hdense : DenseRange gen)
    (hmin : ∀ S : Finset Γ, Subgroup.closure (S : Set Γ) = ⊤ → 5 ≤ S.card)
    (h2 : Nat.card (Work.RelatorRank.contH2 Γ) ≤ 64) : Infinite Γ := by
  by_contra hfin
  haveI : Finite Γ := not_infinite_iff_finite.mp hfin
  haveI : DiscreteTopology Γ := Finite.instDiscreteTopology
  haveI : Fintype Γ := Fintype.ofFinite Γ
  have hbot : IsOpen ((⊥ : Subgroup Γ) : Set Γ) := isOpen_discrete _
  have hQ : IsPGroup 2 Γ := (hpro ⊥ hbot).of_equiv (QuotientGroup.quotientBot (G := Γ))
  have hcl : Subgroup.closure (Set.range gen) = ⊤ := by
    have hd : closure (Set.range gen) = Set.univ := by
      rw [← dense_iff_closure_eq]; exact hdense
    rw [(isClosed_discrete (Set.range gen)).closure_eq] at hd
    rw [hd, Subgroup.closure_univ]
  exact not_subsingleton Γ (subsingleton_of_contH2_le_sixtyfour_of_proPGolodShafarevich h hQ gen hcl hmin h2)

end Work.ProPGS
