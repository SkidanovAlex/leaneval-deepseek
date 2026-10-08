import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV3.Prove.conj_coset_injective
import Submission.Work.ThmF.ChV3.Prove.mul_conj_mem_sdiff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.R_abelian_transitivity`

Sharp transitivity of the `C_Q(P)`-action on the non-trivial cosets of `P` in `R`
(Peterfalvi II, Ch. V §3; the near-field input of step (11), where `R` is shown abelian).

`R` is the preimage in `C_G(P)` of the near-field `F` of step (2) (`Chain15.R`), `N = Ker H Q P t`
its kernel, which step (7) (`h7`) identifies with `P`, and `f = o(st)` its characteristic, so
that `|R| = |P| · f^m` (`h15.hcardR`) with `|C_Q(P)| + 1 = f^m` (`h15.hcq`); the hypothesis
`hpf : |P| = f` then reads `|R| = |P| · (|C_Q(P)| + 1)`.  The multiplicative group
`C_Q(P) = F^×` acts by conjugation on the non-zero elements of the additive group `F = R/P`; by
the fixed-point-freeness clause `h15.hfpf` the action is free, and since `|C_Q(P)| = f^m - 1` is
exactly the number of non-trivial `P`-cosets in `R`, the action is transitive.

The mathematical content is `exists_conj_mem_of_card` below: a free action of a group on a set of
the same cardinality is transitive.  We avoid quotient groups entirely and count the image of the
injective map `↥Y × ↥P → G`, `(y, p) ↦ p * (y * u * y⁻¹)`, whose target `R \ P` has exactly
`|R| - |P| = |Y| * |P|` elements.

The two computational ingredients are proved in separate modules:

* `Work.ThmF.ChV3.Prove.conj_coset_injective` — injectivity of `(y, p) ↦ p * (y u y⁻¹)`,
  which is the contrapositive of `hfpf`;
* `Work.ThmF.ChV3.Prove.mul_conj_mem_sdiff` — its image lies in `R \ P`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

/-- **A free action on a set of the same cardinality is transitive (coset form).**

Let `P ≤ R` be subgroups of a finite group `G`, let `Y ≤ N_G(R) ∩ C_G(P)`, and suppose
`|R| = |P| · (|Y| + 1)` together with fixed-point-freeness of the conjugation action of `Y` on
the non-trivial `P`-cosets of `R` (`hfpf`).  Then any two elements of `R \ P` are conjugate
modulo `P` by an element of `Y`. -/
theorem exists_conj_mem_of_card {G : Type} [Group G] [Finite G] {P R Y : Subgroup G}
    (hPR : P ≤ R) (hYR : Y ≤ Subgroup.normalizer (R : Set G))
    (hYP : Y ≤ Subgroup.centralizer (P : Set G))
    (hcard : Nat.card R = Nat.card P * (Nat.card Y + 1))
    (hfpf : ∀ y ∈ Y, y ≠ 1 → ∀ x ∈ R, x ∉ P → y * x * y⁻¹ * x⁻¹ ∉ P)
    {u v : G} (hu : u ∈ R) (huP : u ∉ P) (hv : v ∈ R) (hvP : v ∉ P) :
    ∃ y ∈ Y, y * u * y⁻¹ * v⁻¹ ∈ P := by
  have hinj : Function.Injective
      (fun w : ↥Y × ↥P => (w.2 : G) * ((w.1 : G) * u * (w.1 : G)⁻¹)) :=
    conj_coset_injective hYP hu huP (fun y hy hy1 => hfpf y hy hy1 u hu huP)
  have hmem : ∀ w : ↥Y × ↥P,
      (w.2 : G) * ((w.1 : G) * u * (w.1 : G)⁻¹) ∈ (R : Set G) \ (P : Set G) :=
    fun w => mul_conj_mem_sdiff hPR hYR hYP hu huP w.1 w.2
  have hrange_ncard :
      (Set.range (fun w : ↥Y × ↥P => (w.2 : G) * ((w.1 : G) * u * (w.1 : G)⁻¹))).ncard
        = ((R : Set G) \ (P : Set G)).ncard := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_prod]
    rw [show ((R : Set G) \ (P : Set G)).ncard = Nat.card R - Nat.card P from by
        rw [Set.ncard_sdiff hPR]; rfl]
    rw [hcard, show Nat.card P * (Nat.card Y + 1) - Nat.card P = Nat.card Y * Nat.card P from by
        rw [Nat.mul_succ, Nat.add_sub_cancel, Nat.mul_comm]]
  have hsub : Set.range (fun w : ↥Y × ↥P => (w.2 : G) * ((w.1 : G) * u * (w.1 : G)⁻¹))
      ⊆ (R : Set G) \ (P : Set G) := by
    rintro x ⟨w, rfl⟩
    exact hmem w
  have hrange : Set.range (fun w : ↥Y × ↥P => (w.2 : G) * ((w.1 : G) * u * (w.1 : G)⁻¹))
      = (R : Set G) \ (P : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq hrange_ncard.symm)
  have hv' : v ∈ Set.range (fun w : ↥Y × ↥P => (w.2 : G) * ((w.1 : G) * u * (w.1 : G)⁻¹)) := by
    rw [hrange]; exact ⟨hv, hvP⟩
  obtain ⟨⟨y, p⟩, hyv⟩ := hv'
  refine ⟨y, y.2, ?_⟩
  have hyv' : (p : G) * ((y : G) * u * (y : G)⁻¹) = v := hyv
  have hmain : (y : G) * u * (y : G)⁻¹ * v⁻¹ = (p : G)⁻¹ := by
    rw [← hyv']; group
  rw [hmain]
  exact P.inv_mem p.2

/-- **Step (11) input: transitivity of `C_Q(P)` on the non-trivial `P`-cosets of `R`.**

`R` is the preimage of the near-field of step (2), `P = Ker H Q P t` (step (7)) is its additive
group of prime order `f = o(st)` (`hpf`), and `C_Q(P)` is the multiplicative group of that field.
Then any two elements of `R \ P` are conjugate modulo `P` by an element of `C_Q(P)`. -/
theorem R_abelian_transitivity {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {u v : G} (hu : u ∈ h15.R) (hv : v ∈ h15.R) (huP : u ∉ P) (hvP : v ∉ P) :
    ∃ y ∈ Work.ThmF.ChV3.CQ Q P, y * u * y⁻¹ * v⁻¹ ∈ P := by
  -- ### `P ≤ R`, from `Ker H Q P t ≤ R` (step (2)) and `Ker H Q P t = P` (step (7))
  have hPR : P ≤ h15.R := by
    intro x hx
    exact h15.hNR (by rw [h7]; exact hx)
  -- ### `C_Q(P) ≤ N_G(R)` (step (2)) and `C_Q(P) ≤ C_G(P)` (definition)
  have hYR : Work.ThmF.ChV3.CQ Q P ≤ Subgroup.normalizer (h15.R : Set G) :=
    le_trans inf_le_right h15.hRn
  have hYP : Work.ThmF.ChV3.CQ Q P ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  -- ### the cardinality hypothesis `|R| = |P| · (|C_Q(P)| + 1)`
  have hcard : Nat.card h15.R = Nat.card P * (Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1) := by
    rw [h15.hcardR, h7, ← h15.hcq, hpf]
  -- ### fixed-point-freeness, transported from `Ker H Q P t` to `P`
  have hfpf' : ∀ y ∈ Work.ThmF.ChV3.CQ Q P, y ≠ 1 → ∀ x ∈ h15.R, x ∉ P →
      y * x * y⁻¹ * x⁻¹ ∉ P := by
    intro y hy hy1 x hx hxP h
    rw [← h7] at h
    exact hy1 (h15.hfpf x hx (by rw [h7]; exact hxP) y hy h)
  exact exists_conj_mem_of_card hPR hYR hYP hcard hfpf' hu huP hv hvP

end Work.ThmF.ChV3.Prove
