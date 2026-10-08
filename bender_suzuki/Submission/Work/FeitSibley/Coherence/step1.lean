import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.Coherence.step2
import Submission.Work.FeitSibley.Coherence.centerMod
import Submission.Work.FeitSibley.Coherence.D_dvd_card_div_sub_one
import Submission.Work.FeitSibley.Coherence.numeric_step1
import Submission.Work.FeitSibley.Coherence.exists_nontrivial_linear_irr
import Submission.Work.FeitSibley.GroupTheory.exists_maximal_normal_below
import Submission.Work.FeitSibley.GroupTheory.commutator_sup_of_commute
import Submission.Work.FeitSibley.Coherence.exists_indQH_of_mem_scriptSR_le_Q
import Submission.Work.FeitSibley.Coherence.centralizing_mod_chief_notMem
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_sup
import Submission.Work.FeitSibley.Coherence.deg_sq_mul_card_le_of_le_center_quotient
import Submission.Work.FeitSibley.Coherence.numeric_step1_assembly
import Submission.Work.FeitSibley.Coherence.commutator_le_of_chief

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.step1`

Peterfalvi II, Appendice XII, step (1) and the abelian case of the Feit–Sibley coherence theorem.

The target of the whole appendix is coherence of `𝒮 = scriptS h.H h.Q1`.  Step (2)
(`Coherence/step2.lean`) reduces it to coherence of `𝒮(S')` (`S' = [S,S]`), so the work here is
to prove `Coherent (𝒮(S'))`.

There are two "easy" families of cases:

* **`Q₁` abelian.**  Then `Q' = [Q,Q] = S'` and `𝒮(S') = 𝒮(Q')`, which is coherent by
  Milestone A (`Coherence/engine.lean`).
* **`|Q₁|` divisible by two primes.**  Then `𝒮(S')` is coherent by the chief-series descent in
  `Q₁` with Feit's criterion.  This is Peterfalvi's step (1).

The remaining case — `Q₁` a nonabelian `p`-group with `p` odd — is Peterfalvi's steps (3)–(8).

## Contents

* `coherent_scriptSR_of_S'_eq_Q'` — coherence of `𝒮(S')` when `S' = Q'`.
* `hlin_of_commutator_Q1_eq_bot` — a nontrivial linear character of `Q₁` when `Q₁` is abelian
  (`[Q₁,Q₁] = ⊥`), the hypothesis `hlin` of `coherent_scriptS_of_coherent_scriptSR`.
* `coherent_scriptS_of_Q1_commutator_bot` — the abelian case of the theorem.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Classical

open scoped commutatorElement

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

/-! ## Coherence of `𝒮(S')` when `S' = Q'` -/

/-- **`𝒮(S')` is coherent when `S' = Q'`.**  Then `𝒮(S') = 𝒮(Q')`, and `𝒮(Q')` is coherent
(Milestone A).  The case `Q₁` abelian is the important instance: `[Q,Q] = [S,S]` there. -/
theorem coherent_scriptSR_of_S'_eq_Q' (h : Work.FeitSibley.FSData G)
    (heq : FSScomm h = FSQcomm h) :
    Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h))
      (Work.FeitSibley.indLin h.H) := by
  rw [heq]
  exact coherent_scriptSR_Qcomm h

/-! ## A nontrivial linear character of an abelian `Q₁` -/

/-- **A nontrivial linear character of `Q₁` when `Q₁` is abelian.**  This is the hypothesis
`hlin` of `coherent_scriptS_of_coherent_scriptSR`: `[Q₁,Q₁] = ⊥` makes `Q₁` commutative, hence
nilpotent, and `Q₁ ≠ ⊥` supplies a non-principal irreducible, which is linear. -/
theorem hlin_of_commutator_Q1_eq_bot (h : Work.FeitSibley.FSData G)
    (hab : ⁅h.Q1, h.Q1⁆ = ⊥) :
    ∃ theta ∈ Work.CharCore.Irr ↥h.Q1,
      theta 1 = 1 ∧ theta ≠ (fun _ : ↥h.Q1 => (1 : ℂ)) := by
  haveI : IsMulCommutative ↥h.Q1 := Subgroup.commutator_self_eq_bot_iff.mp hab
  haveI : Group.IsNilpotent ↥h.Q1 := CommGroup.isNilpotent
  haveI : Nontrivial ↥h.Q1 := (Subgroup.nontrivial_iff_ne_bot h.Q1).mpr h.Q1_ne_bot
  exact exists_nontrivial_linear_irr ↥h.Q1

/-! ## The abelian case of the theorem -/

/-- **The abelian case.**  If `[Q₁,Q₁] = ⊥` then `[Q,Q] = [S,S]`, so `𝒮(S')` is coherent, and
step (2) (`coherent_scriptS_of_coherent_scriptSR`) concludes coherence of `𝒮`. -/
theorem coherent_scriptS_of_Q1_commutator_bot (h : Work.FeitSibley.FSData G)
    (hab : ⁅h.Q1, h.Q1⁆ = ⊥) (heq : FSScomm h = FSQcomm h) :
    Work.Coherence.Coherent (Work.FeitSibley.scriptS h.H h.Q1)
      (Work.FeitSibley.indLin h.H) :=
  coherent_scriptS_of_coherent_scriptSR h (hlin_of_commutator_Q1_eq_bot h hab)
    (coherent_scriptSR_of_S'_eq_Q' h heq)

/-! ## Cardinality lemmas for `D`-invariant sections of `Q₁` -/

/-- For subgroups `A < B` of a finite group, the index `[B : A]` is at least `2`. -/
theorem one_lt_card_div {G : Type} [Group G] [Fintype G] {A B : Subgroup G} (hAB : A ≤ B)
    (hne : A ≠ B) : 1 < Nat.card ↥B / Nat.card ↥A := by
  have hdvd : Nat.card ↥A ∣ Nat.card ↥B := Subgroup.card_dvd_of_le hAB
  have hcard : Nat.card ↥A * (Nat.card ↥B / Nat.card ↥A) = Nat.card ↥B := Nat.mul_div_cancel' hdvd
  have hlt : Nat.card ↥A < Nat.card ↥B := by
    have h1 : A.subgroupOf B ≠ ⊤ := by
      intro htop
      refine hne (le_antisymm hAB ?_)
      intro x hx
      have : (⟨x, hx⟩ : ↥B) ∈ A.subgroupOf B := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    have h2 : 1 < (A.subgroupOf B).index := Subgroup.one_lt_index_of_ne_top h1
    have h3 : Nat.card ↥(A.subgroupOf B) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
    have h4 := Subgroup.card_mul_index (A.subgroupOf B)
    rw [h3] at h4
    have h5 : Nat.card ↥B = Nat.card ↥A * (A.subgroupOf B).index := h4.symm
    rw [h5]
    have hpos : 0 < Nat.card ↥A := Nat.card_pos
    calc Nat.card ↥A = Nat.card ↥A * 1 := (mul_one _).symm
      _ < Nat.card ↥A * (A.subgroupOf B).index := by
          exact Nat.mul_lt_mul_of_pos_left h2 hpos
  have hpos : 0 < Nat.card ↥A := Nat.card_pos
  nlinarith [hcard, hlt, hpos]

/-- **`|D| + 1 ≤ [B : A]` for `A < B` inside `Q₁`.**  `D` acts fixed-point-freely on the
`D`-invariant subgroup `B` and on `A`, so `|D| ∣ |B| - 1` and `|D| ∣ |A| - 1` give
`|D| ∣ |A|·([B : A] - 1)`, and `gcd(|D|, |A|) = 1` because `A ≤ Q₁` and `(|D|, |Q|) = 1`.

This is Peterfalvi's use of "$D$-invariant sections of `Q₁` have order `≡ 1 mod d`" in step (1)
of App. XII. -/
theorem D_add_one_le_card_div {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {A B : Subgroup G} (hAB : A ≤ B) (hB : B ≤ h.Q1)
    (hAn : h.H ≤ Subgroup.normalizer (A : Set G)) (hBn : h.H ≤ Subgroup.normalizer (B : Set G))
    (hne : A ≠ B) : Nat.card h.D + 1 ≤ Nat.card ↥B / Nat.card ↥A := by
  have hA1 : A ≤ h.Q1 := hAB.trans hB
  have hdvdA : h.D ≤ Subgroup.normalizer (A : Set G) := h.D_le_H.trans hAn
  have hdvdB : h.D ≤ Subgroup.normalizer (B : Set G) := h.D_le_H.trans hBn
  have h1 : Nat.card h.D ∣ Nat.card ↥B / Nat.card ↥A - 1 :=
    D_dvd_card_div_sub_one h A B hAB hB hAn hBn
  have h2 : 1 < Nat.card ↥B / Nat.card ↥A := one_lt_card_div hAB hne
  have h3 : 1 ≤ Nat.card ↥B / Nat.card ↥A - 1 := by omega
  have h4 : Nat.card h.D ≤ Nat.card ↥B / Nat.card ↥A - 1 := Nat.le_of_dvd h3 h1
  omega

/-- **`FSQcomm h = FSScomm h ⊔ [Q₁,Q₁]`.**  Since `Q = S ⊔ Q₁` and `S` commutes elementwise with
`Q₁` (`FSData.commute`), the derived subgroup of `Q` splits as the join of the derived subgroups
of the two factors. -/
theorem FSQcomm_eq_sup {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    FSQcomm h = FSScomm h ⊔ ⁅h.Q1, h.Q1⁆ := by
  rw [FSQcomm, FSScomm, ← h.S_sup_Q1]
  exact Work.FeitSibley.GroupTheory.commutator_sup_of_commute h.S h.Q1 h.commute

/-! ## The chief-factor descent (Peterfalvi II, App. XII, step (1)) -/

/-- **The descent step of App. XII (1).**  Let `Q₃ ⊴ Q₂ ⊴ H`, `Q₃ < Q₂`,
`Q₂ ≤ [Q₁,Q₁]`, `Q₂/Q₃` a chief factor of `H` and `Q₂/Q₃ ≤ Z(Q₁/Q₃)`.  If `𝒮(S'Q₂)` is
coherent then so is `𝒮(S'Q₃)`.

This is Feit's criterion (`coherent_of_feit_step`) run against an obstruction
`χ ∈ 𝒮(S'Q₃) ∖ 𝒮(S'Q₂)`: `χ(1) = d·θ(1)` with `θ ∈ Irr(Q₁/Q₃)` non-trivial on `Q₂/Q₃`,
while `∑_{𝒮(S'Q₂)} ξ(1)² = d·[S:S']·(|Q₁/Q₂| - 1)`.  Isaacs 2.30 in `Q₁/Q₃` bounds
`θ(1)²` by `|Q₁ : Z(Q₁/Q₃)|`, and nilpotency of `Q₁` (Thompson, from `D ≠ ⊥`) together with
"`|Q₁|` has two prime divisors" makes `Q₂ ⊊ Z(Q₁/Q₃)`; the `D`-invariant sections then have
order `≡ 1 mod d`, giving the numerical contradiction `numeric_step1_assembly`. -/
theorem coherent_of_chief_descent {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hD : h.D ≠ ⊥)
    (h2 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.card h.Q1 ∧ q ∣ Nat.card h.Q1)
    (Q2 Q3 : Subgroup G) (hQ3Q2 : Q3 ≤ Q2) (hQ2' : Q2 ≤ ⁅h.Q1, h.Q1⁆)
    (hQ2n : h.H ≤ Subgroup.normalizer (Q2 : Set G))
    (hQ3n : h.H ≤ Subgroup.normalizer (Q3 : Set G))
    (hne : Q3 ≠ Q2)
    (hchief : ∀ A : Subgroup G, Q3 ≤ A → A ≤ Q2 → h.H ≤ Subgroup.normalizer (A : Set G) →
      A = Q3 ∨ A = Q2)
    (hcen : ⁅Q2, h.Q1⁆ ≤ Q3)
    (hcoh : Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q2))
      (Work.FeitSibley.indLin h.H)) :
    Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q3))
      (Work.FeitSibley.indLin h.H) := by
  classical
  have hQ1'le : ⁅h.Q1, h.Q1⁆ ≤ h.Q1 :=
    (Subgroup.commutator_le_sup h.Q1 h.Q1).trans (le_of_eq (sup_idem h.Q1))
  have hS'leS : FSScomm h ≤ h.S :=
    (Subgroup.commutator_le_sup h.S h.S).trans (le_of_eq (sup_idem h.S))
  have hQ2Q1 : Q2 ≤ h.Q1 := hQ2'.trans hQ1'le
  have hQ3Q1 : Q3 ≤ h.Q1 := hQ3Q2.trans hQ2Q1
  have hQ3H : Q3 ≤ h.H := hQ3Q1.trans h.Q1_le_H
  haveI hQ3norm : (Q3.subgroupOf h.Q1).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (h.Q1_le_H.trans hQ3n)
  have hQ1nrm : h.Q1 ≤ Subgroup.normalizer (Q3 : Set G) := h.Q1_le_H.trans hQ3n
  -- the ambient data for Feit's criterion
  have hIrr : ∀ x ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q3),
      x ∈ Work.CharCore.Irr ↥h.H :=
    fun x hx => (Finset.mem_filter.mp (scriptSR_subset_scriptS h _ hx)).1
  have hτ : Work.Coherence.IsometryOn (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q3))
      (Work.FeitSibley.indLin h.H) :=
    (Work.FeitSibley.CharQ.isometry_indLin h).mono (scriptSR_subset_scriptS h _)
  have hτV : ∀ α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q3)),
      Work.Coherence.IsVChar (Work.FeitSibley.indLin h.H α) ∧
        Work.FeitSibley.indLin h.H α 1 = 0 :=
    fun α hα => isVChar_indLin_zSpan0_scriptS h
      (Work.Coherence.zSpan0_mono (scriptSR_subset_scriptS h _) hα)
  have hsub : Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q2) ⊆
      Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q3) :=
    scriptSR_subset_of_le h (sup_le_sup_left hQ3Q2 (FSScomm h))
  by_contra hnot
  obtain ⟨χ, hχS, hχS0, hall⟩ :=
    exists_chi_not_coherent hsub hIrr hτ hτV hcoh hnot
  -- `ψ₀ ∈ 𝒮(Q')` has degree `|D|`
  have hFSQ : FSQcomm h = FSScomm h ⊔ ⁅h.Q1, h.Q1⁆ := FSQcomm_eq_sup h
  obtain ⟨ψ₀, hψ₀Q⟩ := scriptSR_Qcomm_nonempty h (exists_nontrivial_linear_of_D_ne_bot h hD)
  have hψ₀S0 : ψ₀ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q2) :=
    scriptSR_subset_of_le h (by rw [hFSQ]; exact sup_le_sup_left hQ2' (FSScomm h)) hψ₀Q
  have hψ₀deg : ψ₀ 1 = (Nat.card h.D : ℂ) :=
    scriptSR_deg_Qcomm h (scriptSR_Qcomm_le_Q h) le_rfl hψ₀Q
  -- the inducing character of `χ`
  have hR3Q : FSScomm h ⊔ Q3 ≤ h.Q :=
    sup_le (hS'leS.trans h.S_le_Q) (hQ3Q1.trans h.Q1_le_Q)
  obtain ⟨φ, hφirr, hφtriv, hχeq, hχdeg⟩ := exists_indQH_of_mem_scriptSR_le_Q h hR3Q hχS
  have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := hIrr χ hχS
  have hdegNat : Work.CharCore.irrDeg χ = Nat.card h.D * Work.CharCore.irrDeg φ := by
    exact_mod_cast hχdeg
  have hχ1 : χ 1 = ((Work.CharCore.irrDeg φ : ℕ) : ℂ) * (ψ₀ 1) := by
    rw [Work.CharCore.irrDeg_spec hχIrr, hψ₀deg, hdegNat]
    push_cast
    ring
  have hineq := hall ψ₀ hψ₀S0 (Work.CharCore.irrDeg φ) hχ1
  have hψ₀Irr : ψ₀ ∈ Work.CharCore.Irr ↥h.H :=
    (Finset.mem_filter.mp (scriptSR_subset_scriptS h _ hψ₀S0)).1
  have hψ₀irr : Work.CharCore.irrDeg ψ₀ = Nat.card h.D := by
    have h1 := Work.CharCore.irrDeg_spec hψ₀Irr
    rw [hψ₀deg] at h1
    exact_mod_cast h1.symm
  -- **The `Z(Q₁/Q₃)` and its properties**
  have hQ2leZ : Q2 ≤ centerMod h Q3 := by
    intro x hx
    rw [mem_centerMod_iff]
    refine ⟨hQ2Q1 hx, fun y hy => ?_⟩
    exact Subgroup.commutator_le.mp hcen x hx y hy
  have hQ3' : Q3 ≤ ⁅h.Q1, h.Q1⁆ := hQ3Q2.trans hQ2'
  obtain ⟨z0, hz0Q1, hz0c, hz0not⟩ :=
    centralizing_mod_chief_notMem h hD h2 Q2 Q3 hQ3Q2 hQ2' hQ3' hQ2n hQ3n hchief hcen
  have hz0Z : z0 ∈ centerMod h Q3 := (mem_centerMod_iff h Q3).mpr ⟨hz0Q1, hz0c⟩
  have hZne : Q2 ≠ centerMod h Q3 := fun heq => hz0not (heq ▸ hz0Z)
  have hZQ1 : centerMod h Q3 ≤ h.Q1 := centerMod_le h Q3
  have hZn : h.H ≤ Subgroup.normalizer (centerMod h Q3 : Set G) := centerMod_normal h Q3 hQ3n
  have hZcen : ∀ x : G, x ∈ centerMod h Q3 → ∀ y : G, y ∈ h.Q1 → x * y * x⁻¹ * y⁻¹ ∈ Q3 :=
    fun x hx => (mem_centerMod_iff h Q3).mp hx |>.2
  have hdeg := deg_sq_mul_card_le_of_le_center_quotient h (centerMod h Q3) Q3 hZQ1 hQ3Q1
    hQ3n hZcen hχS
  -- **The arithmetic inputs**
  have hQIpos : (0:ℝ) < (Nat.card h.Q1 : ℝ) := by
    haveI : Nonempty ↥h.Q1 := ⟨1, h.Q1.one_mem⟩
    exact_mod_cast Nat.card_pos
  have hQ2cpos : (0:ℝ) < (Nat.card ↥Q2 : ℝ) := by
    haveI : Nonempty ↥Q2 := ⟨1, Q2.one_mem⟩
    exact_mod_cast Nat.card_pos
  have hZcpos : (0:ℝ) < (Nat.card ↥(centerMod h Q3) : ℝ) := by
    haveI : Nonempty ↥(centerMod h Q3) := ⟨1, (centerMod h Q3).one_mem⟩
    exact_mod_cast Nat.card_pos
  have hDge1 : (1:ℝ) ≤ (Nat.card h.D : ℝ) := by
    haveI : Nonempty ↥h.D := ⟨1, h.D.one_mem⟩
    exact_mod_cast Nat.card_pos
  have hSScge1 : (1:ℝ) ≤ (Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ) := by
    have hdvd : Nat.card ↥(FSScomm h) ∣ Nat.card ↥h.S := Subgroup.card_dvd_of_le hS'leS
    have hpos : 0 < Nat.card ↥(FSScomm h) := Nat.card_pos
    have h1 : 1 ≤ Nat.card ↥h.S / Nat.card ↥(FSScomm h) :=
      (Nat.le_div_iff_mul_le hpos).mpr (by
        rw [one_mul]
        exact Nat.le_of_dvd Nat.card_pos hdvd)
    exact_mod_cast h1
  have hQ2lt : (Nat.card ↥Q2 : ℝ) < (Nat.card h.Q1 : ℝ) := by
    haveI : Group.IsNilpotent ↥h.Q1 := Q1_isNilpotent_of_D_ne_bot h hD
    have hQ1'lt : ⁅h.Q1, h.Q1⁆ < h.Q1 := commutator_lt_self_of_ne_bot h.Q1 h.Q1_ne_bot
    have hne' : Q2 ≠ h.Q1 := fun heq =>
      (ne_of_lt hQ1'lt) (le_antisymm (heq ▸ hQ2') hQ1'le).symm
    have h1 : Nat.card ↥Q2 < Nat.card ↥h.Q1 := by
      have hdvd : Nat.card ↥Q2 ∣ Nat.card ↥h.Q1 := Subgroup.card_dvd_of_le hQ2Q1
      have hcard : Nat.card ↥Q2 * (Nat.card ↥h.Q1 / Nat.card ↥Q2) = Nat.card ↥h.Q1 :=
        Nat.mul_div_cancel' hdvd
      have h2 : 1 < Nat.card ↥h.Q1 / Nat.card ↥Q2 := one_lt_card_div hQ2Q1 hne'
      nlinarith [hcard, h2, Nat.card_pos (α := ↥Q2)]
    exact_mod_cast h1
  have hsum := sum_deg_sq_scriptSR_sup h Q2 hQ2Q1 hQ2n
  have hz1 : (Nat.card h.D : ℝ) + 1
      ≤ (Nat.card ↥(centerMod h Q3) : ℝ) / (Nat.card ↥Q2 : ℝ) := by
    have hd0 := D_add_one_le_card_div h hQ2leZ hZQ1 hQ2n hZn hZne
    have hdvd : Nat.card ↥Q2 ∣ Nat.card ↥(centerMod h Q3) :=
      Subgroup.card_dvd_of_le hQ2leZ
    have hcast : ((Nat.card ↥(centerMod h Q3) / Nat.card ↥Q2 : ℕ) : ℝ)
        = (Nat.card ↥(centerMod h Q3) : ℝ) / (Nat.card ↥Q2 : ℝ) :=
      Nat.cast_div hdvd hQ2cpos.ne'
    rw [← hcast]
    exact_mod_cast hd0
  have hx2 : (Nat.card h.D : ℝ) + 1
      ≤ (Nat.card h.Q1 : ℝ) / (Nat.card ↥(centerMod h Q3) : ℝ) := by
    have hZneQ1 : centerMod h Q3 ≠ h.Q1 := centerMod_ne_Q1 h Q3 Q2 hQ3Q2 hQ2' hne
    have hd1 := D_add_one_le_card_div h hZQ1 le_rfl hZn h.Q1_normal_in_H hZneQ1
    have hdvd : Nat.card ↥(centerMod h Q3) ∣ Nat.card ↥h.Q1 :=
      Subgroup.card_dvd_of_le hZQ1
    have hcast : ((Nat.card ↥h.Q1 / Nat.card ↥(centerMod h Q3) : ℕ) : ℝ)
        = (Nat.card ↥h.Q1 : ℝ) / (Nat.card ↥(centerMod h Q3) : ℝ) :=
      Nat.cast_div hdvd hZcpos.ne'
    rw [← hcast]
    exact_mod_cast hd1
  have hA : (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
        ((Nat.card h.Q1 : ℝ) / (Nat.card ↥Q2 : ℝ) - 1)
      ≤ 2 * (Nat.card h.D : ℝ) * (Work.CharCore.irrDeg χ : ℝ) := by
    have hcast : ((∑ ξ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q2),
          (Work.CharCore.irrDeg ξ) ^ 2 : ℕ) : ℝ)
        = ∑ ξ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q2),
            ((Work.CharCore.irrDeg ξ : ℝ)) ^ 2 := by push_cast; ring
    have h1 : ((∑ ξ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q2),
          (Work.CharCore.irrDeg ξ) ^ 2 : ℕ) : ℝ)
        ≤ ((2 * Work.CharCore.irrDeg ψ₀ * Work.CharCore.irrDeg χ : ℕ) : ℝ) := by
      exact_mod_cast hineq
    rw [hcast] at h1
    rw [← hsum]
    calc (∑ ξ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q2),
            ((Work.CharCore.irrDeg ξ : ℝ)) ^ 2)
        ≤ ((2 * Work.CharCore.irrDeg ψ₀ * Work.CharCore.irrDeg χ : ℕ) : ℝ) := h1
      _ = 2 * (Nat.card h.D : ℝ) * (Work.CharCore.irrDeg χ : ℝ) := by
          push_cast [hψ₀irr]
          ring
  exact numeric_step1_assembly hDge1 hSScge1 hQ2cpos hZcpos hQIpos (Nat.cast_nonneg _) hQ2lt hA
    hdeg hz1 hx2

/-! ## `H` normalises the derived subgroup of `Q₁` -/

/-- `H` normalises `[Q₁,Q₁]`: `H` normalises `Q₁`, so conjugation by `H` is an automorphism of
`Q₁` and therefore carries its derived subgroup to itself. -/
theorem H_le_normalizer_commutator_Q1 {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) :
    h.H ≤ Subgroup.normalizer ((⁅h.Q1, h.Q1⁆ : Subgroup G) : Set G) := by
  have hmem : ∀ x ∈ h.H, (h.Q1).map (MulAut.conj x).toMonoidHom = h.Q1 := by
    intro x hx
    have hiff : ∀ y : G, y ∈ (h.Q1 : Set G) ↔ (MulAut.conj x) y ∈ (h.Q1 : Set G) := by
      intro y
      simpa [MulAut.conj_apply] using
        (Subgroup.mem_set_normalizer_iff.mp (h.Q1_normal_in_H hx) y)
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hiff z).mp hz
    · intro hy
      refine ⟨(MulAut.conj x).symm y, (hiff _).mpr ?_, MulEquiv.apply_symm_apply _ y⟩
      rw [MulEquiv.apply_symm_apply]
      exact hy
  rw [Subgroup.le_normalizer_iff]
  intro t ht k hk
  have hmap : (⁅h.Q1, h.Q1⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom = ⁅h.Q1, h.Q1⁆ := by
    rw [Subgroup.map_commutator, hmem t ht]
  show (MulAut.conj t) k ∈ (⁅h.Q1, h.Q1⁆ : Subgroup G)
  have hthis : (MulAut.conj t) k
      ∈ (⁅h.Q1, h.Q1⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom := ⟨k, hk, rfl⟩
  rwa [hmap] at hthis

/-! ## Step (1): `𝒮(S')` is coherent for `|Q₁|` divisible by two primes -/

/-- **Peterfalvi II, App. XII, step (1).**  If `D ≠ 1` (so `Q₁` is nilpotent, by Thompson) and
`|Q₁|` is divisible by two distinct primes, then `𝒮(S')` is coherent.

The proof descends a chief series in `Q₁`: `𝒮(S'[Q₁,Q₁]) = 𝒮(Q')` is coherent (Milestone A),
and `coherent_of_chief_descent` passes from `𝒮(S'Q₂)` to `𝒮(S'Q₃)` for every chief factor
`Q₂/Q₃`; minimality of `Q₂` among coherent chief factors forces `Q₂ = ⊥`, i.e. coherence of
`𝒮(S')` itself. -/
theorem coherent_scriptSR_of_two_primes {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (hD : h.D ≠ ⊥)
    (h2 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.card h.Q1 ∧ q ∣ Nat.card h.Q1) :
    Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h))
      (Work.FeitSibley.indLin h.H) := by
  classical
  have hN : FSScomm h ⊔ ⁅h.Q1, h.Q1⁆ = FSQcomm h := (FSQcomm_eq_sup h).symm
  have hNn : h.H ≤ Subgroup.normalizer ((⁅h.Q1, h.Q1⁆ : Subgroup G) : Set G) := H_le_normalizer_commutator_Q1 h
  -- the predicate whose minimal value we take
  let P : ℕ → Prop := fun n => ∃ Q2 : Subgroup G, Q2 ≤ ⁅h.Q1, h.Q1⁆ ∧
    h.H ≤ Subgroup.normalizer (Q2 : Set G) ∧ Nat.card Q2 = n ∧
    Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q2))
      (Work.FeitSibley.indLin h.H)
  have hbase : P (Nat.card ↥(⁅h.Q1, h.Q1⁆)) :=
    ⟨⁅h.Q1, h.Q1⁆, le_rfl, hNn, rfl, by rw [hN]; exact coherent_scriptSR_Qcomm h⟩
  have hex : ∃ n, P n := ⟨_, hbase⟩
  obtain ⟨Q2, hQ2le, hQ2n, hQ2card, hQ2coh⟩ := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, ¬ P k := fun k hk => Nat.find_min hex hk
  by_cases hQ2bot : Q2 = ⊥
  · rw [hQ2bot, sup_bot_eq] at hQ2coh
    exact hQ2coh
  · -- `Q₂ ≠ ⊥`: descend one chief factor and contradict minimality
    obtain ⟨Q3, hQ3le, hQ3ne, hQ3n, hchief⟩ :=
      Work.FeitSibley.GroupTheory.exists_maximal_normal_below h.H Q2 hQ2n hQ2bot
    have hQ3Q2 : Q3 ≤ Q2 := hQ3le
    have hQ3' : Q3 ≤ ⁅h.Q1, h.Q1⁆ := hQ3le.trans hQ2le
    have hcen : ⁅Q2, h.Q1⁆ ≤ Q3 :=
      commutator_le_of_chief h hD Q2 Q3 hQ3Q2 hQ2le hQ2n hQ3n hQ3ne hchief
    have hdescent := coherent_of_chief_descent h hD h2 Q2 Q3 hQ3Q2 hQ2le hQ2n hQ3n hQ3ne hchief
      hcen hQ2coh
    have hlt : Nat.card ↥Q3 < Nat.card ↥Q2 := by
      have hdvd : Nat.card ↥Q3 ∣ Nat.card ↥Q2 := Subgroup.card_dvd_of_le hQ3le
      have hcard : Nat.card ↥Q3 * (Nat.card ↥Q2 / Nat.card ↥Q3) = Nat.card ↥Q2 :=
        Nat.mul_div_cancel' hdvd
      have h2' : 1 < Nat.card ↥Q2 / Nat.card ↥Q3 := one_lt_card_div hQ3le hQ3ne
      nlinarith [hcard, h2', Nat.card_pos (α := ↥Q3)]
    exact (hmin (Nat.card ↥Q3) (by rw [← hQ2card]; exact hlt)
      ⟨Q3, hQ3', hQ3n, rfl, hdescent⟩).elim

end Work.FeitSibley.Coherence
