import Mathlib
import Submission.Work.FeitSibley.Coherence.step1
import Submission.Work.FeitSibley.Coherence.step2
import Submission.Work.FeitSibley.Coherence.irr_congr_mod_card_Q
import Submission.Work.FeitSibley.Coherence.scriptSR_Qcomm_nonempty
import Submission.Work.FeitSibley.Coherence.cfInner_indLin_scriptS
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_sdiff
import Submission.Work.FeitSibley.Coherence.coherent_union_two_blocks
import Submission.Work.FeitSibley.CharQ.degree_D_scriptS
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.FeitSibley.GroupTheory.D_dvd_card_sub_one
import Submission.Work.Coherence.cfInner_eq_zero_of_two_coherent_blocks
import Submission.Work.Coherence.cfInner_eq_zero_of_two_coherent_blocks_vchar
import Submission.Work.FeitSibley.Coherence.exists_lambda_T_rho
import Submission.Work.FeitSibley.Coherence.cfInner_v_rho
import Submission.Work.FeitSibley.Coherence.swap_negate_lift
import Submission.Work.FeitSibley.Coherence.two_block_norm_dichotomy
import Submission.Work.FeitSibley.Coherence.a_dvd_lambda_two_block
import Submission.Work.Coherence.vchar_relation_dichotomy
import Submission.Work.Coherence.coherent_mono
import Submission.Work.FeitSibley.Coherence.coherent_scriptS_sub_FSZ
import Submission.Work.FeitSibley.Coherence.X_coherent_of_X1
import Submission.Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR
import Submission.Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr
import Submission.Work.CharPrelim.ft4_1
import Submission.Work.Coherence.NormIrr
import Submission.Work.Coherence.Coherent
import Submission.Work.Induction.frobenius_reciprocity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.coherent_scriptSR_of_pgroup`

Peterfalvi II, Appendice XII, steps (4)–(8): for the Feit–Sibley data `h` with `D ≠ ⊥` and `Q₁`
a non-abelian `p`-group (`p` odd), coherence of `𝒳 = 𝒮 ∖ 𝒮(Z)` (`Z = FSZ h = [Q₁,Q₁] ∩ Z(Q₁)`)
implies coherence of `𝒮(S')` (`S' = [S,S]`).

The two-block argument of the source runs as follows.  Put `𝒴 = 𝒮(Q')` (coherent by Milestone A)
and `𝒳 = 𝒮 ∖ 𝒮(Z)` (coherent by hypothesis).  Choosing `χ₁ ∈ 𝒳` of minimal degree and `η₁ ∈ 𝒴`
(all of whose elements have degree `d = |D|`), one produces coherent extensions `σ` of `𝒳` and `ρ`
of `𝒴` whose images are mutually orthogonal and satisfy the *cross relation*
`Ind(χ₁ - a·η₁) = σ χ₁ - a·ρ η₁` with `a = χ₁(1)/d` (steps (5)–(8); the congruence of step (7),
`irr_congr_mod_card_Q`, enters through `a ∣ λ`).  `coherent_union_two_blocks` then makes
`𝒳 ∪ 𝒴` coherent, and Feit's criterion (`coherent_of_feit_step`) extends coherence to `𝒮(S')`,
using `χ(1)² ≤ ∑_{𝒳₁} ξ(1)²` (`𝒳₁ = 𝒳 ∩ 𝒮(S')`) for the remaining characters.

## Status (after the session of the two `card` lemmas)

Proved here (sorry-free):

* the `FSZ` API (`FSZ_le_Q1'`, `FSZ_le_Q'`, `FSZ_le_H'`, `FSZ_normal_in_H'`, `FSZ_commute_Q'`,
  `FSZ_ne_bot'`, `FSZ_card_ge'`, `FSZ_not_inv`, `FSQcomm_ge_FSZ`, `FSScomm_le_FSQcomm`, …);
* `sum_deg_chi_sdiff_FSZ` — the regular-character identity of step (8);
* `two_le_card_sdiff_FSZ` — `|𝒳| ≥ 2` (via `Σ_{χ∈𝒳}χ(1)² = |H|·(|Z|−1)/|Z| > 0` from
  `sum_deg_sq_scriptSR_sdiff_gen h ⊥ (FSZ h)` together with `deg_sq_le_of_mem_scriptSR h ⊥ ⊥`
  giving `χ(1)² ≤ |D|²·[Q₁ : Z]`, and `2|D| + 1 ≤ |Z|` from
  `two_mul_card_D_add_one_le_card_of_odd` with `Odd |Z|`);
* `two_le_card_scriptSR_Qcomm` — `|𝒴| ≥ 2` (via `sum_deg_sq_scriptSR_sup` at `Q₂ = Q₁'`, the
  constant degree `|D|` of members of `𝒴`, and `[Q₁ : Q₁'] − 1 ≥ 2|D|` from
  `D_dvd_card_sub_one`, oddness of `[Q₁ : Q₁']` and of `|D|`);
* `exists_prodChar_of_mem_scriptSR_FSScomm` — a character of `𝒮(S')` is `Ind_Q^H(prodChar λ θ)`
  with `λ` linear (trivial on `S'`), so `irrDeg χ = |D|·irrDeg θ` for some `θ ∈ Irr Q₁`.

Further proved in the next session:

* `exists_prodChar_of_mem_scriptSR_FSScomm` — a character of `𝒮(S')` is `Ind_Q^H(prodChar λ θ)`
  with `λ` linear, so `irrDeg χ = |D|·irrDeg θ` for some `θ ∈ Irr Q₁` (this is the degree input
  of both remaining lemmas);
* `p_le_irrDeg_of_nontrivial_on_commutator` — if `θ ∈ Irr Q₁` is non-trivial at an element of
  `Q₁' = [Q₁,Q₁]` then `p ≤ irrDeg θ` (a linear character kills the derived subgroup, via
  `Subgroup.commutator_le` + `MonoidHom.mem_ker` in the abelian group `ℂˣ`);
* `feitsibley_final_ineq` — the Feit-criterion bound of step (6);
* `exists_prodChar_deg_of_mem_sdiff_FSZ` — a character of `𝒳 = 𝒮∖𝒮(Z)` is
  `Ind_Q^H(prodChar λ θ)` with `θ` non-trivial at an element of `Z`, and
  `irrDeg χ = |D|·irrDeg λ·irrDeg θ` (this plus the `p`-power structure of `irrDeg θ` — from
  `irr_degree_dvd` and `Nat.eq_prime_pow_of_unique_prime_dvd` — gives the degree divisibility
  `∀ x ∈ 𝒳, ∃ k : ℤ, x 1 = k · x₀ 1` at a minimal-degree `x₀`, hence `hdegX` in
  `two_block_relation`);
* `exists_lift_pair_orthogonal` — steps (4)–(5): the extensions `σ` (from `hcoh`) and `ρ` (from
  `coherent_scriptSR_Qcomm h`), their agreement with `Ind_H^G` on `ℤ[𝒳]⁰`/`ℤ[𝒴]⁰`, their isometry
  and virtual-character properties, and the mutual orthogonality of their images (via the
  colleague-proved `Work.Coherence.cfInner_eq_zero_of_two_coherent_blocks_vchar`, which is
  imported here);
* the closing contradiction of the main theorem;
* the closing contradiction at the end of `coherent_scriptSR_of_pgroup` (test Feit's criterion
  with the witness `y₀ ∈ 𝒴 ⊆ S₀` and `d = irrDeg χ / |D|`, using
  `exists_prodChar_of_mem_scriptSR_FSScomm` for the divisibility `|D| ∣ irrDeg χ`).

**`two_block_relation` (the crux, steps (4)–(8)) is proved below as well**, so the main theorem
`coherent_scriptSR_of_pgroup` is sorry-free.  Its proof is assembled from three colleague-proved
modules — `Coherence/exists_lambda_T_rho` (the `λ`-decomposition of `T = Ind(x₀ - a·y₀)`),
`Coherence/a_dvd_lambda_two_block` (step (8), `a ∣ λ`) and `Coherence/two_block_norm_dichotomy`
(the norm inequality: `λ = 0`, or `λ = a` and `|𝒴| = 2`) — together with the in-file lemmas
`cfInner_indLin_T_rho_sub`, `cfInner_indLin_T_self`, `exists_lift_pair_orthogonal`,
`exists_min_deg_sdiff_FSZ` and `Work.Coherence.vchar_relation_dichotomy` (the `-1` relation
`v = σχ₁` or `v = -σχ₂`), and the swap–negate lemma `Coherence/swap_negate_lift`, which handles
the exceptional cases (`λ = a`, `|𝒴| = 2`, and the mirror case `v = -σχ₂`, `|𝒳| = 2`) by
replacing a lift `τ` on a two-element orthonormal set by the negated swap on its two elements.

Note on dependencies: `Coherence/a_dvd_lambda_two_block` cannot import this file (that would be
an import cycle), so the `Z`-lemmas it needs are also available, under `_aux` names, in the
standalone module `Coherence/FSZ_aux`, which it imports instead.

### Obstacle to record for `two_block_relation`

`cfInner_eq_zero_of_two_coherent_blocks` asks for a *single* `δ` with `δ • σ x ∈ Irr G` for all
`x` in the block, while a coherent extension only yields `σ x ∈ ±Irr G` with signs that may vary
with `x`.  The clean fix is a normalisation lemma "a coherent set has an extension whose values
on the set are irreducible": define `σ' := σ ∘ u` where `u` is the `ℤ`-linear endomorphism of
`ℤ[X]` negating the basis elements whose sign is `−1` (extended to `H → ℂ` by, say,
`u f = ∑_{x ∈ X} (cfInner f x) • (ε x • x)`); then `σ' x ∈ Irr G` for all `x`, and `σ'` still
agrees with `τ` on `ℤ[X]⁰` and is still an isometry.  Alternatively, re-prove the orthogonality
with per-element signs (the existing proof only uses `⟨ψ, ψ'⟩ ∈ {0,1}` for irreducibles).

### API notes gathered while proving the above (useful for the remaining pieces)

* `Work.CharCore.linear_char_iff_deg_one (hθ : θ ∈ Irr G) : irrDeg θ = 1 ↔ ∃ φ, ∀ g, θ g = ↑(φ g)`.
  To turn `θ` non-trivial on `Q₁'` into `|D| ∣ irrDeg χ ⟹ irrDeg θ ≥ p` one needs "a linear
  character kills the derived subgroup", i.e. `φ z = 1` for `z ∈ commutator ↥h.Q1`; the ready
  route is `Subgroup.commutator_def` (`⁅H₁,H₂⁆ = closure {g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁,g₂⁆ = g}`)
  plus `Subgroup.closure_induction` and `commutatorElement_eq_one_iff_mul_comm` in the abelian
  group `ℂˣ` (the `rw [Subgroup.map_commutator]` route needs the identification
  `commutator ↥h.Q1 = ⁅⊤,⊤⁆`, which I did not find a lemma for).
* `Work.CharCore.irr_degree_dvd : ∃ d, χ 1 = ↑d ∧ d ∣ Nat.card G`; the witness `d` is `irrDeg χ`
  via `irrDeg_spec`.
* `Work.CharCore.irrKer χ hχ : Subgroup G` with `coe_irrKer : (irrKer χ hχ : Set G) = charKernel χ`
  and `mem_charKernel : g ∈ charKernel χ ↔ χ g = χ 1`; `Subgroup.subgroupOf_sup (hA : A ≤ B)
  (hA' : A' ≤ B) : (A ⊔ A').subgroupOf B = A.subgroupOf B ⊔ A'.subgroupOf B` — these give the
  `𝒮(Z) ∩ 𝒮(S') = 𝒮(S' ⊔ Z)` bookkeeping in step 4 of the plan below.
* `Finset.sum_le_sum_of_subset_of_nonneg` for `∑_{𝒳∩𝒮(S')} ≤ ∑_{S₀}`.
* Confirmed signatures: `Work.FeitSibley.CharQ.prodChar_apply_of_mem_Q1` (`prodChar λ θ x =
  λ 1 · θ x` for `x ∈ Q₁`), `prodChar_apply_of_mem_S` (in namespace `Work.FeitSibley.Coherence`),
  `Work.FeitSibley.CharQ.scriptS_eq_image`, `Work.FeitSibley.Coherence.mem_scriptSR_indQH_iff`,
  `mem_scriptSR_prodChar_iff`, `Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr`,
  `Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel`,
  `Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR`, `Work.CharPrelim.ft4_1`.

### Plan for `feitsibley_final_ineq`

With `χ ∈ 𝒮(S') ∖ S₀`, `S₀ = (𝒳 ∩ 𝒮(S')) ∪ 𝒴`:

1. `χ ∉ 𝒴` gives, through `mem_scriptSR_indQH_iff` (at `Z = Q'`) and
   `indQH_apply_eq_one_of_triv_on_Z`, an element of `Q₁'` at which the inducing `θ` is
   non-trivial (use `mem_scriptSR_prodChar_iff`/`prodChar_apply_of_mem_Q1` to pass between `θ`
   and `prodChar λ θ`, and `irrKer` + `subgroupOf_sup` for the `S' ⊔ Q₁' = Q'` bookkeeping);
2. hence `θ(1) > 1`; as `Q₁` is an odd `p`-group, `θ(1)` is an odd divisor of `p^n`, so
   `θ(1) ≥ p ≥ 3`, giving `2·|D|·χ(1) = 2|D|²θ(1) ≤ (2/3)·χ(1)²`;
3. `χ(1)² = |D|²θ(1)² ≤ |D|²·[Q₁ : Z(Q₁)] ≤ |D|·[S : S']·(|Q₁| − |Q₁ : Z|)`
   (the last step is `|D| ≤ |S:S'|(|Z|−1)`, as `2|D| + 1 ≤ |Z|`);
4. `∑_{ξ ∈ 𝒳∩𝒮(S')} ξ(1)² = |D|·[S : S']·(|Q₁| − |Q₁ : Z|)` is `sum_deg_sq_scriptSR_sdiff`
   (the two sets `(𝒮∖𝒮(Z)) ∩ 𝒮(S')` and `𝒮(S') ∖ 𝒮(S' ⊔ Z)` agree because `{x | ξ x = ξ 1}` is a
   subgroup for `ξ ∈ Irr H`, i.e. `irrKer`), and `∑_{S₀} ≥ ∑_{𝒳∩𝒮(S')}`.

### Plan for `two_block_relation` (crux)

Take the canonical lifts `σ` (from `hcoh`) and `ρ` (from `coherent_scriptSR_Qcomm`), normalised so
that all values are irreducible (`isometry_image_irr` + negating basis elements).  With
`x₀ ∈ 𝒳` of minimal degree, `a := x₀(1)/|D| ≥ 2`, `y₀ ∈ 𝒴` (all degrees `|D|`), and
`T := indLin(x₀ − a·y₀)`:

1. `c_j := ⟨T, ρ y_j⟩ ∈ ℤ` is constant `= λ` for `j ≠ 1` and `λ − a` for `j = 1`, by the
   isometry on `ℤ[𝒮]⁰` (`χ_j − a_j x₀ ∈ ℤ[𝒳]⁰`) and `v := T − Σ_j c_j ρ y_j ⊥ ρ𝒴`
   (`cfInner_int_vchar` for integrality);
2. `1 + a² = (λ−a)² + (|𝒴|−1)λ² + ⟨v,v⟩`; with `a ∣ λ` (step (8): `irr_congr_mod_card_Q`
   applied to `±ρy₀`, which is constant on `Z^#` because
   `e'_1(z) − e'_1(1) = −|Q|(λ/a + μ)` — this is exactly `sum_deg_chi_sdiff_FSZ` plus the
   decomposition of `Res_H^G e'_1` in `Irr H`) and `|𝒴| ≥ 2`, `a ≥ 2`, one gets `λ = 0`;
3. `v = ±Irr G` of norm 1, and `⟨Ind(χ_2 − χ_1), T⟩ = −1` with any `χ_2 ∈ 𝒳`, `χ_2 ≠ x₀` of
   ratio `a_2 ≥ 2` (Case A) or, if all ratios are `1` (Case B), with any `χ_2 ≠ x₀` (then
   `|𝒳| ≥ 3` forces `v = e_1`, and `|𝒳| = 2` is handled by the swap–negate lift).  In Case A the
   strict computation forces `v = e_1 = σ x₀`, giving the cross relation
   `T = σ x₀ − a ρ y₀`.  (`|𝒳| ≥ 2` is `two_le_card_sdiff_FSZ`.)
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open Classical
open scoped commutatorElement

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

/-! ## Basic facts about `Z = FSZ h = [Q₁,Q₁] ∩ C_G(Q₁)` -/

theorem FSZ_le_Q1' (h : Work.FeitSibley.FSData G) : FSZ h ≤ h.Q1 :=
  (inf_le_left.trans (Subgroup.commutator_le_sup h.Q1 h.Q1)).trans (le_of_eq (sup_idem h.Q1))

theorem FSZ_le_Q' (h : Work.FeitSibley.FSData G) : FSZ h ≤ h.Q :=
  (FSZ_le_Q1' h).trans h.Q1_le_Q

theorem FSZ_le_H' (h : Work.FeitSibley.FSData G) : FSZ h ≤ h.H :=
  (FSZ_le_Q1' h).trans h.Q1_le_H

theorem H_le_normalizer_centralizer_Q1 (h : Work.FeitSibley.FSData G) :
    h.H ≤ Subgroup.normalizer (Subgroup.centralizer (h.Q1 : Set G)) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx z hz
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro q hq
  have hx' : x⁻¹ ∈ h.H := h.H.inv_mem hx
  have hq' : x⁻¹ * q * (x⁻¹)⁻¹ ∈ h.Q1 :=
    (Subgroup.mem_set_normalizer_iff.mp (h.Q1_normal_in_H hx') q).mp hq
  have h1 : x⁻¹ * q * (x⁻¹)⁻¹ * z = z * (x⁻¹ * q * (x⁻¹)⁻¹) := hz _ hq'
  calc q * (x * z * x⁻¹) = x * ((x⁻¹ * q * (x⁻¹)⁻¹) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * q * (x⁻¹)⁻¹)) * x⁻¹ := by rw [h1]
    _ = (x * z * x⁻¹) * q := by group

theorem FSZ_normal_in_H' (h : Work.FeitSibley.FSData G) :
    h.H ≤ Subgroup.normalizer (FSZ h : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx z hz
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.le_normalizer_iff.mp (H_le_normalizer_commutator_Q1 h) x hx z hz1,
     Subgroup.le_normalizer_iff.mp (H_le_normalizer_centralizer_Q1 h) x hx z hz2⟩

/-- `Z = [Q₁,Q₁] ∩ C_G(Q₁)` is central in `Q = S·Q₁`. -/
theorem FSZ_commute_Q' (h : Work.FeitSibley.FSData G) {z : G} (hz : z ∈ FSZ h) :
    ∀ q ∈ h.Q, z * q = q * z := by
  have hzc : z ∈ Subgroup.centralizer (h.Q1 : Set G) := (Subgroup.mem_inf.mp hz).2
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_Q_decomp hq
  have h1 : z * a = a * z := (h.commute a ha z (FSZ_le_Q1' h hz)).symm
  have h2 : z * b = b * z := (Subgroup.mem_centralizer_iff.mp hzc b hb).symm
  calc z * (a * b) = z * a * b := by rw [mul_assoc]
    _ = a * z * b := by rw [h1]
    _ = a * (z * b) := by rw [mul_assoc]
    _ = a * (b * z) := by rw [h2]
    _ = a * b * z := by rw [mul_assoc]

/-- In a nilpotent group, `[X,X] ∩ Z(X) ≠ 1` whenever `[X,X] ≠ 1`. -/
theorem commutator_inf_center_ne_bot {X : Type*} [Group X] (hX : Group.IsNilpotent X)
    (hX' : commutator X ≠ ⊥) :
    commutator X ⊓ Subgroup.center X ≠ ⊥ := by
  haveI : Group.IsNilpotent ↥(⊤ : Subgroup X) := Group.isNilpotent_top.mpr hX
  have hex : ∃ m, (⊤ : Subgroup X).lowerCentralSeries m = ⊥ :=
    (Subgroup.isNilpotent_iff_lowerCentralSeries (⊤ : Subgroup X)).mp ‹_›
  have hspec : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex) = ⊥ := Nat.find_spec hex
  have htop_ne : (⊤ : Subgroup X) ≠ ⊥ := by
    intro htop
    exact hX' (eq_bot_iff.mpr (by rw [← htop]; exact le_top))
  have hNpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, Subgroup.lowerCentralSeries_zero] at hspec
      exact absurd hspec htop_ne
    · exact h
  have hN2 : 2 ≤ Nat.find hex := by
    by_contra hcon
    have hle : Nat.find hex = 0 ∨ Nat.find hex = 1 := by omega
    rcases hle with h | h
    · rw [h, Subgroup.lowerCentralSeries_zero] at hspec
      exact absurd hspec htop_ne
    · rw [h, Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero,
          Subgroup.commutator_comm] at hspec
      exact hX' hspec
  have hprev : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1) ≠ ⊥ := by
    intro hc
    exact Nat.find_min hex (by omega) hc
  have hstep : ⁅(⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1), (⊤ : Subgroup X)⁆ = ⊥ := by
    have h1 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [← Subgroup.lowerCentralSeries_succ, h1, hspec]
  have hcen : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1) ≤ Subgroup.center X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hstep
    exact Subgroup.mem_centralizer_iff.mp (hle hz) g (Subgroup.mem_top g)
  have hle' : (⊤ : Subgroup X).lowerCentralSeries (Nat.find hex - 1) ≤ commutator X := by
    have hmono := Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup X)
      (by omega : 1 ≤ Nat.find hex - 1)
    rwa [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero,
      Subgroup.commutator_comm] at hmono
  intro hc
  refine hprev (le_bot_iff.mp ?_)
  exact (le_inf hle' hcen).trans (le_of_eq hc)

theorem FSZ_ne_bot' (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hpg : IsPGroup p h.Q1) (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) : FSZ h ≠ ⊥ := by
  intro hbot
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Group.IsNilpotent ↥h.Q1 := hpg.isNilpotent
  have hcomm : commutator ↥h.Q1 ≠ ⊥ := by
    intro hc
    apply hab
    have hmap := Subgroup.map_subtype_commutator h.Q1
    rw [← hmap, hc, Subgroup.map_bot]
  have hne := commutator_inf_center_ne_bot (X := ↥h.Q1) ‹Group.IsNilpotent ↥h.Q1› hcomm
  apply hne
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have hx1' : (x : G) ∈ ⁅h.Q1, h.Q1⁆ := by
    have hmap := Subgroup.map_subtype_commutator h.Q1
    rw [← hmap]
    exact ⟨x, hx1, rfl⟩
  have hx2' : (x : G) ∈ Subgroup.centralizer (h.Q1 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h2 := Subgroup.mem_center_iff.mp hx2 ⟨q, hq⟩
    exact congrArg Subtype.val h2
  have hmem : (x : G) ∈ FSZ h := Subgroup.mem_inf.mpr ⟨hx1', hx2'⟩
  rw [hbot] at hmem
  exact Subtype.ext (Subgroup.mem_bot.mp hmem)

theorem FSZ_card_ge' (h : Work.FeitSibley.FSData G) (hne : FSZ h ≠ ⊥) :
    Nat.card h.D + 1 ≤ Nat.card ↥(FSZ h) := by
  have hdvd : Nat.card h.D ∣ Nat.card ↥(FSZ h) - 1 :=
    Work.FeitSibley.GroupTheory.D_dvd_card_sub_one h (FSZ h) (FSZ_le_Q1' h)
      (h.D_le_H.trans (FSZ_normal_in_H' h))
  have h2 : 2 ≤ Nat.card ↥(FSZ h) :=
    Work.FeitSibley.FSData.two_le_card_of_ne_bot (FSZ h) hne
  have h1 : 0 < Nat.card ↥(FSZ h) - 1 := by omega
  have hle : Nat.card h.D ≤ Nat.card ↥(FSZ h) - 1 := Nat.le_of_dvd h1 hdvd
  omega

/-- An element of a `p`-group (`p ≠ 2`) squaring to `1` is trivial. -/
theorem Q1_eq_one_of_sq_eq_one (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1) {z : G} (hz : z ∈ h.Q1) (hz2 : z ^ 2 = 1) :
    z = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
  have hdvd1 : orderOf (⟨z, hz⟩ : ↥h.Q1) ∣ p ^ n := by
    rw [← hn]; exact orderOf_dvd_natCard _
  have hdvd2 : orderOf (⟨z, hz⟩ : ↥h.Q1) ∣ 2 := by
    rw [(Subgroup.orderOf_coe (⟨z, hz⟩ : ↥h.Q1)).symm]
    exact orderOf_dvd_of_pow_eq_one hz2
  have hcop : Nat.Coprime 2 (p ^ n) :=
    (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)).pow_right n
  have hg : orderOf (⟨z, hz⟩ : ↥h.Q1) ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]; exact Nat.dvd_gcd hdvd2 hdvd1
  have h1 : (⟨z, hz⟩ : ↥h.Q1) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  simpa using Subtype.ext_iff.mp h1

/-- `Z` is not inverted by any element of `G`. -/
theorem FSZ_not_inv (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : IsPGroup p h.Q1) {z : G} (hz : z ∈ FSZ h) (hz1 : z ≠ 1) :
    ∀ g : G, g * z * g⁻¹ ≠ z⁻¹ := by
  intro g hg
  have hzQ1 : z ∈ h.Q1 := FSZ_le_Q1' h hz
  by_cases hgH : g ∈ h.H
  · obtain ⟨q, hq, dd, hd, rfl⟩ := h.mem_H_decomp hgH
    have hw : dd * z * dd⁻¹ = z⁻¹ := by
      have hqw : q * (dd * z * dd⁻¹) * q⁻¹ = z⁻¹ := by
        rw [show q * (dd * z * dd⁻¹) * q⁻¹ = q * dd * z * (q * dd)⁻¹ by group]
        exact hg
      calc dd * z * dd⁻¹ = q⁻¹ * (q * (dd * z * dd⁻¹) * q⁻¹) * q := by group
        _ = q⁻¹ * z⁻¹ * q := by rw [hqw]
        _ = q⁻¹ * (z⁻¹ * q) := by group
        _ = q⁻¹ * (q * z⁻¹) := by
            have hz' : z⁻¹ ∈ FSZ h := (FSZ h).inv_mem hz
            rw [FSZ_commute_Q' h hz' q hq]
        _ = z⁻¹ := by group
    by_cases hdd1 : dd = 1
    · rw [hdd1] at hw
      simp at hw
      have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_inv_eq.mpr hw.symm
      exact hz1 (Q1_eq_one_of_sq_eq_one h hp hp2 hpg hzQ1 hz2)
    · have hdd2' : (dd * dd) * z * (dd * dd)⁻¹ = z := by
        calc (dd * dd) * z * (dd * dd)⁻¹ = dd * (dd * z * dd⁻¹) * dd⁻¹ := by group
          _ = dd * z⁻¹ * dd⁻¹ := by rw [hw]
          _ = (dd * z * dd⁻¹)⁻¹ := by group
          _ = (z⁻¹)⁻¹ := by rw [hw]
          _ = z := by group
      have hdd2D : dd * dd ∈ h.D := h.D.mul_mem hd hd
      have hdd2ne : dd * dd ≠ 1 := by
        intro hc
        have hdvd2 : orderOf dd ∣ 2 :=
          orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc)
        have hdvdD : orderOf dd ∣ Nat.card h.D := by
          have h1 : orderOf dd = orderOf (⟨dd, hd⟩ : ↥h.D) :=
            Subgroup.orderOf_coe (⟨dd, hd⟩ : ↥h.D)
          rw [h1]
          simpa using orderOf_dvd_natCard (⟨dd, hd⟩ : ↥h.D)
        have hcop : Nat.Coprime 2 (Nat.card h.D) := Nat.coprime_two_left.mpr h.D_odd
        have hg1 : orderOf dd ∣ 1 := by
          rw [← Nat.Coprime.gcd_eq_one hcop]
          exact Nat.dvd_gcd hdvd2 hdvdD
        exact hdd1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg1))
      exact hz1 (h.D_fpf_Q1 (dd * dd) hdd2D hdd2ne z hzQ1 hdd2')
  · have hTI := h.Q_TI g hgH
    have hzQ : z ∈ h.Q := h.Q1_le_Q hzQ1
    have hzg : z ∈ Submission.Blueprint.conj g h.Q := by
      rw [Submission.Blueprint.conj, Subgroup.mem_map]
      refine ⟨z⁻¹, h.Q.inv_mem hzQ, ?_⟩
      change g * z⁻¹ * g⁻¹ = z
      rw [show g * z⁻¹ * g⁻¹ = (g * z * g⁻¹)⁻¹ by group, hg]
      group
    have : z ∈ (⊥ : Subgroup G) := by
      rw [← hTI]; exact Subgroup.mem_inf.mpr ⟨hzQ, hzg⟩
    exact hz1 (Subgroup.mem_bot.mp this)

/-- `𝒴 = 𝒮(Q') ⊆ 𝒮(Z)` since `Z ≤ [Q₁,Q₁] ≤ Q'`. -/
theorem FSQcomm_ge_FSZ (h : Work.FeitSibley.FSData G) : FSZ h ≤ FSQcomm h := by
  rw [FSQcomm]
  exact inf_le_left.trans (Subgroup.commutator_mono h.Q1_le_Q h.Q1_le_Q)

/-- `S' = [S,S] ≤ [Q,Q] = Q'`. -/
theorem FSScomm_le_FSQcomm (h : Work.FeitSibley.FSData G) : FSScomm h ≤ FSQcomm h := by
  rw [FSScomm, FSQcomm]
  exact Subgroup.commutator_mono h.S_le_Q h.S_le_Q


/-! ## The remaining inputs of the two-block argument -/

/-- `𝒳 = 𝒮∖𝒮(Z)` has at least two elements (relevant for the orthogonality of step (5)).

The sum of the squared degrees over `𝒳` is `∑_{χ ∈ 𝒳} χ(1)² = |H| - |H/Z| > 0`
(`sum_deg_sq_scriptSR_sdiff_gen` with `S₁ = ⊥`), while every `χ ∈ 𝒳 ⊆ 𝒮` has
`χ(1)² ≤ |D|²·[Q₁ : Z]` (`deg_sq_le_of_mem_scriptSR`).  If `𝒳` were a single character `χ`
this would give `|Q₁| - |Q₁ : Z| ≤ |D|·|Q₁ : Z|`, i.e. `|Z| - 1 ≤ |D|`, contradicting
`2·|D| + 1 ≤ |Z|` (`two_mul_card_D_add_one_le_card_of_odd`, applicable since `|Z|` is odd). -/
theorem two_le_card_sdiff_FSZ {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {p : ℕ} (hp : p.Prime) (hpg : IsPGroup p h.Q1) (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) :
    2 ≤ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)).card := by
  classical
  have hZQ1 : FSZ h ≤ h.Q1 := FSZ_le_Q1' h
  have hZn : h.H ≤ Subgroup.normalizer (FSZ h : Set G) := FSZ_normal_in_H' h
  have hZe : FSZ h ≠ ⊥ := FSZ_ne_bot' h hp hpg hab
  have hp2 : p ≠ 2 := fun h2 => h.Q1_not_two (h2 ▸ hpg)
  have hDpos : (0 : ℝ) < (Nat.card h.D : ℝ) := by
    haveI : Nonempty ↥h.D := ⟨⟨1, h.D.one_mem⟩⟩
    exact_mod_cast Nat.card_pos
  have hSpos : (0 : ℝ) < (Nat.card h.S : ℝ) := by
    haveI : Nonempty ↥h.S := ⟨⟨1, h.S.one_mem⟩⟩
    exact_mod_cast Nat.card_pos
  have hQpos : (0 : ℝ) < (Nat.card h.Q1 : ℝ) := by
    haveI : Nonempty ↥h.Q1 := ⟨⟨1, h.Q1.one_mem⟩⟩
    exact_mod_cast Nat.card_pos
  have hZpos : (0 : ℝ) < (Nat.card ↥(FSZ h) : ℝ) := by
    haveI : Nonempty ↥(FSZ h) := ⟨⟨1, (FSZ h).one_mem⟩⟩
    exact_mod_cast Nat.card_pos
  have hDge1 : (1 : ℝ) ≤ (Nat.card h.D : ℝ) := by
    haveI : Nonempty ↥h.D := ⟨⟨1, h.D.one_mem⟩⟩
    have h1 : 0 < Nat.card ↥h.D := Nat.card_pos
    exact_mod_cast h1
  -- `[Q₁ : Z]` as a natural number
  have hZidx : ((FSZ h).subgroupOf h.Q1).index = Nat.card h.Q1 / Nat.card ↥(FSZ h) := by
    have hdvd : Nat.card ↥(FSZ h) ∣ Nat.card h.Q1 := Subgroup.card_dvd_of_le hZQ1
    have hcard : Nat.card ↥((FSZ h).subgroupOf h.Q1) = Nat.card ↥(FSZ h) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ1).toEquiv
    have hmul := Subgroup.card_mul_index ((FSZ h).subgroupOf h.Q1)
    rw [hcard] at hmul
    have hpos : 0 < Nat.card ↥(FSZ h) := by
      haveI : Nonempty ↥(FSZ h) := ⟨⟨1, (FSZ h).one_mem⟩⟩
      exact Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [hmul, Nat.mul_div_cancel' hdvd]
  -- the index of `⊥` in `S`
  have hbotidx : ((⊥ : Subgroup G).subgroupOf h.S).index = Nat.card h.S := by
    have h1 : (⊥ : Subgroup G).subgroupOf h.S = ⊥ := by
      ext x
      simp [Subgroup.subgroupOf]
    rw [h1, Subgroup.index_bot]
  have hHnormbot : h.H ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    simp
  -- the sum of squared degrees over `𝒳`
  have hsum :=
    Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_sdiff_gen h (⊥ : Subgroup G) (FSZ h)
      bot_le hHnormbot hZQ1 hZn
  rw [scriptSR_bot, bot_sup_eq] at hsum
  rw [hbotidx, hZidx] at hsum
  rw [Nat.cast_div (Subgroup.card_dvd_of_le hZQ1)
    (by haveI : Nonempty ↥(FSZ h) := ⟨⟨1, (FSZ h).one_mem⟩⟩
        exact_mod_cast (Nat.card_pos (α := ↥(FSZ h))).ne')] at hsum
  -- the degree bound
  have hcent : ⁅h.S, (⊥ : Subgroup G)⁆ ≤ ⊥ := by simp
  have hbound : ∀ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
      ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 ≤ (Nat.card h.D : ℝ) ^ 2 * (Nat.card h.S : ℝ) *
        ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) := by
    intro χ hχ
    have hχS : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (⊥ : Subgroup G) := by
      rw [scriptSR_bot]
      exact (Finset.mem_sdiff.mp hχ).1
    have hb := Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR h (⊥ : Subgroup G)
      (⊥ : Subgroup G) bot_le bot_le le_rfl hcent hχS
    rwa [hbotidx] at hb
  -- `|Z|` is odd, hence `2·|D| + 1 ≤ |Z|`
  have hZodd : Odd (Nat.card ↥(FSZ h)) := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
    have hdvd : Nat.card ↥(FSZ h) ∣ p ^ n := by
      rw [← hn]
      exact Subgroup.card_dvd_of_le hZQ1
    have hne0 : Nat.card ↥(FSZ h) ≠ 0 := by
      haveI : Nonempty ↥(FSZ h) := ⟨⟨1, (FSZ h).one_mem⟩⟩
      exact Nat.card_pos.ne'
    have hpow : Nat.card ↥(FSZ h) = p ^ (Nat.card ↥(FSZ h)).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hne0 (fun {q} hq hqdvd => by
        have hqp : q ∣ p := hq.dvd_of_dvd_pow (hqdvd.trans hdvd)
        rcases hp.eq_one_or_self_of_dvd q hqp with h1 | h2
        · exact absurd h1 hq.ne_one
        · exact h2)
    rw [hpow]
    exact (hp.odd_of_ne_two hp2).pow
  have hZge : (2 : ℝ) * (Nat.card h.D : ℝ) + 1 ≤ (Nat.card ↥(FSZ h) : ℝ) := by
    have h0 := Work.FeitSibley.Coherence.two_mul_card_D_add_one_le_card_of_odd h (FSZ h)
      hZQ1 (h.D_le_H.trans hZn) hZe hZodd
    exact_mod_cast h0
  by_contra hcon
  have hcard1 : (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)).card ≤ 1 := by omega
  -- `𝒳` is nonempty
  have hnonempty : (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hsum
    simp only [Finset.sum_empty] at hsum
    have hlt : (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ) < (Nat.card h.Q1 : ℝ) := by
      rw [div_lt_iff₀ hZpos]
      nlinarith [hZpos, hQpos, hDge1, hZge]
    have hRpos : 0 < (Nat.card h.D : ℝ) * (Nat.card h.S : ℝ) *
        ((Nat.card h.Q1 : ℝ) - (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) :=
      mul_pos (mul_pos hDpos hSpos) (by linarith)
    linarith
  obtain ⟨χ, hχ⟩ := hnonempty
  have hsingle : (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) = {χ} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hχ, ?_⟩
    intro y hy
    by_contra hne
    have h2 : 2 ≤ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)).card := by
      have hsub : ({χ, y} : Finset (↥h.H → ℂ)) ⊆ (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · rw [hz]; exact hχ
        · rw [hz]; exact hy
      have hle := Finset.card_le_card hsub
      rwa [Finset.card_pair (Ne.symm hne)] at hle
    omega
  have hdeg : ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 = (Nat.card h.D : ℝ) * (Nat.card h.S : ℝ) *
      ((Nat.card h.Q1 : ℝ) - (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) := by
    rw [hsingle, Finset.sum_singleton] at hsum
    exact hsum
  have hbd := hbound χ hχ
  have hle : (Nat.card h.D : ℝ) * (Nat.card h.S : ℝ) *
      ((Nat.card h.Q1 : ℝ) - (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ))
      ≤ ((Nat.card h.D : ℝ) * (Nat.card h.S : ℝ)) *
        ((Nat.card h.D : ℝ) * ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ))) := by
    rw [hdeg] at hbd
    nlinarith [hbd]
  have hdS : (0 : ℝ) < (Nat.card h.D : ℝ) * (Nat.card h.S : ℝ) := mul_pos hDpos hSpos
  have hkey : (Nat.card h.Q1 : ℝ) - (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)
      ≤ (Nat.card h.D : ℝ) * ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) :=
    le_of_mul_le_mul_left hle hdS
  have hkey2 := mul_le_mul_of_nonneg_right hkey (le_of_lt hZpos)
  rw [sub_mul, div_mul_cancel₀ _ hZpos.ne', mul_assoc, div_mul_cancel₀ _ hZpos.ne',
    mul_comm] at hkey2
  have hzed : (Nat.card ↥(FSZ h) : ℝ) - 1 ≤ (Nat.card h.D : ℝ) := by
    nlinarith [hkey2, hQpos]
  nlinarith [hzed, hZge, hDge1]

/-- `𝒴 = 𝒮(Q')` has at least two elements.

Every `χ ∈ 𝒴` has degree `|D|` (`scriptSR_Qcomm_deg`), so
`∑_{χ ∈ 𝒴} χ(1)² = |𝒴|·|D|²`, while `sum_deg_sq_scriptSR_sup` gives this same sum as
`|D|·[S : S']·([Q₁ : Q₁'] - 1)`.  Since `[Q₁ : Q₁']` is a `p`-power (`p` odd, so odd) with
`|D| ∣ [Q₁ : Q₁'] - 1` and `|D|` odd, we get `[Q₁ : Q₁'] - 1 ≥ 2|D|`, whence `|𝒴| ≥ 2`. -/
theorem two_le_card_scriptSR_Qcomm {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime) (hpg : IsPGroup p h.Q1)
    (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) :
    2 ≤ (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)).card := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h2 => h.Q1_not_two (h2 ▸ hpg)
  have hQ1'Q1 : ⁅h.Q1, h.Q1⁆ ≤ h.Q1 :=
    (Subgroup.commutator_le_sup h.Q1 h.Q1).trans (le_of_eq (sup_idem h.Q1))
  have hQ1'n : h.H ≤ Subgroup.normalizer (⁅h.Q1, h.Q1⁆ : Subgroup G) :=
    H_le_normalizer_commutator_Q1 h
  -- the sum of the squared degrees over `𝒴`
  have hsum := Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_sup h ⁅h.Q1, h.Q1⁆ hQ1'Q1 hQ1'n
  rw [← FSQcomm_eq_sup h] at hsum
  -- every member of `𝒴` has degree `|D|`
  have hdeg : ∀ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
      (Work.CharCore.irrDeg χ : ℝ) = (Nat.card h.D : ℝ) := by
    intro χ hχ
    have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H :=
      (Finset.mem_filter.mp (scriptSR_subset_scriptS h (FSQcomm h) hχ)).1
    have h1 : χ 1 = (Nat.card h.D : ℂ) := scriptSR_Qcomm_deg h hχ
    have h2 : Work.CharCore.irrDeg χ = Nat.card h.D := by
      have hc : ((Work.CharCore.irrDeg χ : ℕ) : ℂ) = ((Nat.card h.D : ℕ) : ℂ) := by
        rw [← Work.CharCore.irrDeg_spec hχIrr, h1]
      exact Nat.cast_injective hc
    exact_mod_cast h2
  have hsum2 : (∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
        ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
      = ((Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)).card : ℝ) * (Nat.card h.D : ℝ) ^ 2 := by
    rw [Finset.sum_congr rfl (fun χ hχ => by rw [hdeg χ hχ]), Finset.sum_const, nsmul_eq_mul]
  -- arithmetic on `q = [Q₁ : Q₁']`
  have hcardQ1'dvd : Nat.card ↥⁅h.Q1, h.Q1⁆ ∣ Nat.card h.Q1 := Subgroup.card_dvd_of_le hQ1'Q1
  have hQ1'pos : 0 < Nat.card ↥⁅h.Q1, h.Q1⁆ := by
    haveI : Nonempty ↥⁅h.Q1, h.Q1⁆ := ⟨⟨1, (⁅h.Q1, h.Q1⁆).one_mem⟩⟩
    exact Nat.card_pos
  have hQ1pos : 0 < Nat.card h.Q1 := by
    haveI : Nonempty ↥h.Q1 := ⟨⟨1, h.Q1.one_mem⟩⟩
    exact Nat.card_pos
  have hQeq : Nat.card h.Q1 = (Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆) *
      Nat.card ↥⁅h.Q1, h.Q1⁆ := by
    rw [mul_comm]
    exact (Nat.mul_div_cancel' hcardQ1'dvd).symm
  have hcop : Nat.Coprime (Nat.card h.D) (Nat.card ↥⁅h.Q1, h.Q1⁆) :=
    h.coprime_D_Q.coprime_dvd_right (hcardQ1'dvd.trans (Subgroup.card_dvd_of_le h.Q1_le_Q))
  have hdvd1 : Nat.card h.D ∣ Nat.card h.Q1 - 1 := by
    have hmem : h.D ≤ Subgroup.normalizer (h.Q1 : Set G) := h.D_le_H.trans h.Q1_normal_in_H
    exact Work.FeitSibley.GroupTheory.D_dvd_card_sub_one h h.Q1 le_rfl hmem
  have hdvd2 : Nat.card h.D ∣ Nat.card ↥⁅h.Q1, h.Q1⁆ - 1 := by
    have hmem : h.D ≤ Subgroup.normalizer (⁅h.Q1, h.Q1⁆ : Subgroup G) := h.D_le_H.trans hQ1'n
    exact Work.FeitSibley.GroupTheory.D_dvd_card_sub_one h ⁅h.Q1, h.Q1⁆ hQ1'Q1 hmem
  have hdvdq : Nat.card h.D ∣ Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ - 1 := by
    have hAleQ : Nat.card ↥⁅h.Q1, h.Q1⁆ ≤ Nat.card h.Q1 :=
      Nat.le_of_dvd hQ1pos hcardQ1'dvd
    have hQA : Nat.card h.Q1 - Nat.card ↥⁅h.Q1, h.Q1⁆ =
        (Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ - 1) * Nat.card ↥⁅h.Q1, h.Q1⁆ := by
      nth_rewrite 1 [hQeq]
      rw [Nat.mul_sub_right_distrib, one_mul]
    have hsub : Nat.card h.D ∣
        (Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ - 1) * Nat.card ↥⁅h.Q1, h.Q1⁆ := by
      have hd := Nat.dvd_sub hdvd1 hdvd2
      rw [show Nat.card h.Q1 - 1 - (Nat.card ↥⁅h.Q1, h.Q1⁆ - 1)
          = Nat.card h.Q1 - Nat.card ↥⁅h.Q1, h.Q1⁆ by omega, hQA] at hd
      exact hd
    exact hcop.dvd_of_dvd_mul_right hsub
  have hq_ge : 2 ≤ Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ := by
    have hne : ⁅h.Q1, h.Q1⁆ ≠ h.Q1 := by
      intro heq
      haveI : Group.IsNilpotent ↥h.Q1 := hpg.isNilpotent
      exact (ne_of_lt (commutator_lt_self_of_ne_bot h.Q1 h.Q1_ne_bot)) heq
    have h1 := D_add_one_le_card_div h hQ1'Q1 le_rfl hQ1'n h.Q1_normal_in_H hne
    have h2 : 1 ≤ Nat.card ↥h.D := by
      haveI : Nonempty ↥h.D := ⟨⟨1, h.D.one_mem⟩⟩
      exact Nat.card_pos
    omega
  have hq_odd : Odd (Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆) := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
    have hdvd : Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ ∣ p ^ n := by
      rw [← hn]
      exact Nat.div_dvd_of_dvd hcardQ1'dvd
    have hne0 : Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ ≠ 0 := by omega
    have hpow : Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆
        = p ^ (Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hne0 (fun {q} hq hqdvd => by
        have hqp : q ∣ p := hq.dvd_of_dvd_pow (hqdvd.trans hdvd)
        rcases hp.eq_one_or_self_of_dvd q hqp with h1 | h2
        · exact absurd h1 hq.ne_one
        · exact h2)
    rw [hpow]
    exact (hp.odd_of_ne_two hp2).pow
  have hq2 : 2 * Nat.card h.D ≤ Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ - 1 := by
    obtain ⟨m, hm⟩ := hdvdq
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hm
      omega
    have heven : Even m := by
      rcases Nat.even_or_odd m with he | ho
      · exact he
      · exfalso
        have hodd1 : Odd (Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ - 1) := by
          rw [hm]
          exact h.D_odd.mul ho
        rcases hq_odd with ⟨a, ha⟩
        rcases hodd1 with ⟨b, hb⟩
        omega
    rw [hm]
    have hm2 : 2 ≤ m := by
      rcases heven with ⟨k, hk⟩
      omega
    calc 2 * Nat.card h.D = Nat.card h.D * 2 := by ring
      _ ≤ Nat.card h.D * m := Nat.mul_le_mul_left _ hm2
  -- the summation identity, in `ℝ`
  have hs : (1 : ℝ) ≤ (Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ) := by
    have hS'leS : Nat.card ↥(FSScomm h) ≤ Nat.card ↥h.S :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (FSScomm_le_S h))
    rw [le_div_iff₀]
    · simpa using hS'leS
    · haveI : Nonempty ↥(FSScomm h) := ⟨⟨1, (FSScomm h).one_mem⟩⟩
      exact_mod_cast Nat.card_pos
  have hqR : 2 * (Nat.card h.D : ℝ) ≤
      (Nat.card h.Q1 : ℝ) / (Nat.card ↥⁅h.Q1, h.Q1⁆ : ℝ) - 1 := by
    have hcast : ((Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ : ℕ) : ℝ)
        = (Nat.card h.Q1 : ℝ) / (Nat.card ↥⁅h.Q1, h.Q1⁆ : ℝ) :=
      Nat.cast_div hcardQ1'dvd (by exact_mod_cast hQ1'pos.ne')
    have hsub_cast : ((Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆ - 1 : ℕ) : ℝ)
        = (Nat.card h.Q1 : ℝ) / (Nat.card ↥⁅h.Q1, h.Q1⁆ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Nat.card h.Q1 / Nat.card ↥⁅h.Q1, h.Q1⁆),
        Nat.cast_one, hcast]
    rw [← hsub_cast]
    exact_mod_cast hq2
  have hDge1 : (1 : ℝ) ≤ (Nat.card h.D : ℝ) := by
    haveI : Nonempty ↥h.D := ⟨⟨1, h.D.one_mem⟩⟩
    have h1 : 1 ≤ Nat.card ↥h.D := Nat.card_pos
    exact_mod_cast h1
  have hcard_ge : (2 : ℝ) ≤ ((Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)).card : ℝ) := by
    have hkey : ((Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)).card : ℝ) * (Nat.card h.D : ℝ) ^ 2
        = (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
          ((Nat.card h.Q1 : ℝ) / (Nat.card ↥⁅h.Q1, h.Q1⁆ : ℝ) - 1) := by
      rw [← hsum2, hsum]
    have hge : (2 : ℝ) * (Nat.card h.D : ℝ) ^ 2
        ≤ ((Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)).card : ℝ) * (Nat.card h.D : ℝ) ^ 2 := by
      rw [hkey]
      have hd0 : (0 : ℝ) ≤ (Nat.card h.D : ℝ) := by linarith [hDge1]
      have hqq0 : (0 : ℝ) ≤ (Nat.card h.Q1 : ℝ) / (Nat.card ↥⁅h.Q1, h.Q1⁆ : ℝ) - 1 := by
        linarith [hqR, hDge1]
      have hstep1 : (2 : ℝ) * (Nat.card h.D : ℝ) ^ 2
          ≤ (Nat.card h.D : ℝ) * ((Nat.card h.Q1 : ℝ) / (Nat.card ↥⁅h.Q1, h.Q1⁆ : ℝ) - 1) := by
        nlinarith [hqR, hDge1]
      have hstep2 : (Nat.card h.D : ℝ) * ((Nat.card h.Q1 : ℝ) / (Nat.card ↥⁅h.Q1, h.Q1⁆ : ℝ) - 1)
          ≤ (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
            ((Nat.card h.Q1 : ℝ) / (Nat.card ↥⁅h.Q1, h.Q1⁆ : ℝ) - 1) := by
        nlinarith [hs, hqR, hDge1, hd0, hqq0]
      linarith [hstep1, hstep2]
    have hd2 : (0 : ℝ) < (Nat.card h.D : ℝ) ^ 2 := by positivity
    nlinarith [hge, hd2]
  exact_mod_cast hcard_ge

/-- **Steps (4)–(5): the coherent extensions and the orthogonality of their images.**  From
coherence of `𝒳` (hypothesis) and of `𝒴` (Milestone A) one gets extensions `σ`, `ρ` agreeing with
`Ind_H^G` on the respective degree-zero lattices, with virtual-character values, and whose images
are mutually orthogonal (`cfInner_eq_zero_of_two_coherent_blocks_vchar`, applicable because
`|𝒳| ≥ 2` and `|𝒴| ≥ 2`). -/
theorem exists_lift_pair_orthogonal {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hD : h.D ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1)
    (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥)
    (hcoh : Work.Coherence.Coherent (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) (Work.FeitSibley.indLin h.H)) :
    ∃ (σ ρ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)),
      (∀ α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)), σ α = Work.FeitSibley.indLin h.H α) ∧
      Work.Coherence.IsometryOnAll (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) σ ∧
      (∀ x ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)), Work.Coherence.IsVChar (σ x)) ∧
      (∀ α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)),
          ρ α = Work.FeitSibley.indLin h.H α) ∧
      Work.Coherence.IsometryOnAll (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) ρ ∧
      (∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h), Work.Coherence.IsVChar (ρ y)) ∧
      (∀ x ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
          Work.Coherence.cfInner (σ x) (ρ y) = 0) := by
  classical
  obtain ⟨σ, hσ0, hσiso, hσV⟩ := hcoh
  obtain ⟨ρ, hρ0, hρiso, hρV⟩ := coherent_scriptSR_Qcomm h
  have hXY : Disjoint (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h))
      (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) := by
    rw [Finset.disjoint_left]
    intro x hx hxy
    exact (Finset.mem_sdiff.mp hx).2 (scriptSR_subset_of_le h (FSQcomm_ge_FSZ h) hxy)
  have hsub : (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∪
        Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)
      ⊆ Work.FeitSibley.scriptS h.H h.Q1 :=
    Finset.union_subset Finset.sdiff_subset (scriptSR_subset_scriptS h _)
  have hIrr : ∀ x ∈ Work.FeitSibley.scriptS h.H h.Q1, x ∈ Work.CharCore.Irr ↥h.H :=
    fun x hx => (Finset.mem_filter.mp hx).1
  have hτ : Work.Coherence.IsometryOn (Work.FeitSibley.scriptS h.H h.Q1)
      (Work.FeitSibley.indLin h.H) := Work.FeitSibley.CharQ.isometry_indLin h
  have hτV : ∀ α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1),
      Work.FeitSibley.indLin h.H α 1 = 0 := fun α hα =>
    (isVChar_indLin_zSpan0_scriptS h hα).2
  have hσV' : ∀ x ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)), Work.CharCore.IsVChar (σ x) :=
    fun x hx => (Work.CharCore.IsVChar_iff_coherence (σ x)).mpr (hσV x hx)
  have hρV' : ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
      Work.CharCore.IsVChar (ρ y) :=
    fun y hy => (Work.CharCore.IsVChar_iff_coherence (ρ y)).mpr (hρV y hy)
  have horth := Work.Coherence.cfInner_eq_zero_of_two_coherent_blocks_vchar hXY hsub hIrr hτ
    hτV hσ0 hσiso hσV' hρ0 hρiso hρV'
    (two_le_card_sdiff_FSZ h hp hpg hab) (two_le_card_scriptSR_Qcomm h hp hpg hab)
  exact ⟨σ, ρ, hσ0, hσiso, hσV, hρ0, hρiso, hρV, horth⟩

/-- The regular-character identity of Peterfalvi II, App. XII step (8):
`∑_{χ ∈ 𝒳} χ(1)·(χ(z) − χ(1)) = −|H|` for `z ∈ Z^#`. -/
theorem sum_deg_chi_sdiff_FSZ {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {z : G} (hz : z ∈ FSZ h) (hz1 : z ≠ 1) :
    (∑ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        (χ 1) * χ ⟨z, FSZ_le_H' h hz⟩)
      - (∑ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        (χ 1) * χ 1)
      = -(Nat.card h.H : ℂ) := by
  classical
  set X : Finset (↥h.H → ℂ) := Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h) with hX
  have hXsub : X ⊆ Work.CharCore.Irr ↥h.H := fun χ hχ =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hχ).1).1
  have hzH : (⟨z, FSZ_le_H' h hz⟩ : ↥h.H) ≠ 1 := fun hc => hz1 (Subtype.ext_iff.mp hc)
  have hzero : (∑ χ ∈ (Work.CharCore.Irr ↥h.H \ X),
      ((χ 1) * χ ⟨z, FSZ_le_H' h hz⟩ - (χ 1) * χ 1)) = 0 := by
    refine Finset.sum_eq_zero fun χ hχ => ?_
    rw [Finset.mem_sdiff] at hχ
    obtain ⟨hχIrr, hχX⟩ := hχ
    have hval : χ ⟨z, FSZ_le_H' h hz⟩ = χ 1 := by
      by_cases hχS : χ ∈ Work.FeitSibley.scriptS h.H h.Q1
      · have hχZ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h) := by
          by_contra hc
          exact hχX (Finset.mem_sdiff.mpr ⟨hχS, hc⟩)
        exact (mem_scriptSR_iff h (FSZ h)).mp hχZ |>.2 ⟨z, FSZ_le_H' h hz⟩ hz
      · have hall : ∀ x : ↥h.H, (x : G) ∈ h.Q1 → χ x = χ 1 := by
          intro x hx
          by_contra hc
          exact hχS (Finset.mem_filter.mpr ⟨hχIrr, ⟨x, hx, hc⟩⟩)
        exact hall ⟨z, FSZ_le_H' h hz⟩ (FSZ_le_Q1' h hz)
    rw [hval]; ring
  have hsum_eq : (∑ χ ∈ X, ((χ 1) * χ ⟨z, FSZ_le_H' h hz⟩ - (χ 1) * χ 1))
      = ∑ χ ∈ Work.CharCore.Irr ↥h.H,
          ((χ 1) * χ ⟨z, FSZ_le_H' h hz⟩ - (χ 1) * χ 1) := by
    have hs := Finset.sum_sdiff (f := fun χ : ↥h.H → ℂ =>
      ((χ 1) * χ ⟨z, FSZ_le_H' h hz⟩ - (χ 1) * χ 1)) hXsub
    rw [← hs, hzero, zero_add]
  have hreg : (∑ χ ∈ Work.CharCore.Irr ↥h.H,
      ((χ 1) * χ ⟨z, FSZ_le_H' h hz⟩ - (χ 1) * χ 1))
      = (Work.CharCore.regularChar ↥h.H) ⟨z, FSZ_le_H' h hz⟩
        - (Work.CharCore.regularChar ↥h.H) 1 := by
    have h1 : (∑ χ ∈ Work.CharCore.Irr ↥h.H, (χ 1) * χ ⟨z, FSZ_le_H' h hz⟩)
        = (∑ χ ∈ Work.CharCore.Irr ↥h.H, (Work.CharCore.irrDeg χ : ℂ) • χ)
            ⟨z, FSZ_le_H' h hz⟩ := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun χ hχ => by
        rw [Pi.smul_apply, smul_eq_mul, Work.CharCore.irrDeg_spec hχ]
    have h2 : (∑ χ ∈ Work.CharCore.Irr ↥h.H, (χ 1) * χ 1)
        = (∑ χ ∈ Work.CharCore.Irr ↥h.H, (Work.CharCore.irrDeg χ : ℂ) • χ) 1 := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun χ hχ => by
        rw [Pi.smul_apply, smul_eq_mul, Work.CharCore.irrDeg_spec hχ]
    rw [Finset.sum_sub_distrib, h1, h2, ← Work.CharCore.regularChar_eq_sum]
  rw [hX] at hsum_eq ⊢
  rw [← Finset.sum_sub_distrib, hsum_eq, hreg]
  simp [Work.CharCore.regularChar, hzH]

/-- **The `prodChar` decomposition of a character of `𝒮(S')`.**  A character `χ ∈ 𝒮(S')` of the
Feit–Sibley data is induced from `prodChar λ θ` with `λ ∈ Irr S` trivial on `S'` (hence linear)
and `θ ∈ Irr Q₁`; in particular `irrDeg χ = |D| · irrDeg θ`. -/
theorem exists_prodChar_of_mem_scriptSR_FSScomm {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {χ : ↥h.H → ℂ}
    (hχ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h)) :
    ∃ (lam : ↥h.S → ℂ) (θ : ↥h.Q1 → ℂ),
      lam ∈ Work.CharCore.Irr ↥h.S ∧ θ ∈ Work.CharCore.Irr ↥h.Q1 ∧
      χ = h.indQH (h.prodChar lam θ) ∧
      (∀ z : ↥h.S, ((z : ↥h.S) : G) ∈ FSScomm h → lam z = lam 1) ∧
      Work.CharCore.irrDeg lam = 1 ∧
      Work.CharCore.irrDeg χ = Nat.card h.D * Work.CharCore.irrDeg θ := by
  classical
  have hχS : χ ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hχ
  obtain ⟨φ, hφirr, -, hχeq⟩ := (Work.FeitSibley.CharQ.scriptS_eq_image h).mp hχS
  obtain ⟨lam, hlam, θ, hθ, hφeq⟩ := Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr h hφirr
  have hθ1 : θ 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hθ]
    exact Work.CharCore.irrDeg_ne_zero hθ
  have hFSSn : h.H ≤ Subgroup.normalizer (FSScomm h : Set G) := H_le_normalizer_FSScomm h
  have hFSSQ : FSScomm h ≤ h.Q := (FSScomm_le_S h).trans h.S_le_Q
  have hφtriv : ∀ z : ↥h.Q, (z : G) ∈ FSScomm h → φ z = φ 1 :=
    (mem_scriptSR_indQH_iff h hφirr (by rw [← hχeq]; exact hχS) hFSSQ hFSSn).mp
      (by rw [← hχeq]; exact hχ)
  have hlamtriv : ∀ z : ↥h.S, ((z : ↥h.S) : G) ∈ FSScomm h → lam z = lam 1 := by
    intro z hz
    have h1 := hφtriv ⟨((z : ↥h.S) : G), h.S_le_Q z.2⟩ hz
    rw [hφeq, Work.FeitSibley.Coherence.prodChar_apply_of_mem_S h lam θ _ z.2,
      Work.FeitSibley.FSData.prodChar_one] at h1
    exact mul_right_cancel₀ hθ1 h1
  have hM : _root_.commutator ↥h.S ≤ (FSScomm h).subgroupOf h.S :=
    Work.FeitSibley.Coherence.commutator_le_FSScomm_subgroupOf h
  haveI : ((FSScomm h).subgroupOf h.S).Normal := Subgroup.Normal.of_commutator_le _ hM
  have hlam1 : Work.CharCore.irrDeg lam = 1 :=
    Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel hM hlam
      (fun z hz => (Work.CharCore.mem_charKernel).mpr (hlamtriv z hz))
  have hφθ : Work.CharCore.irrDeg φ = Work.CharCore.irrDeg θ := by
    have h3 : ((Work.CharCore.irrDeg φ : ℕ) : ℂ) = ((Work.CharCore.irrDeg θ : ℕ) : ℂ) := by
      rw [← Work.CharCore.irrDeg_spec hφirr, hφeq, Work.FeitSibley.FSData.prodChar_one,
        Work.CharCore.irrDeg_spec hlam, Work.CharCore.irrDeg_spec hθ, hlam1]
      ring
    exact Nat.cast_injective h3
  have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχS).1
  have hdegχ : Work.CharCore.irrDeg χ = Nat.card h.D * Work.CharCore.irrDeg φ := by
    have h1 : χ 1 = (Nat.card h.D : ℂ) * (φ 1) := by
      rw [hχeq, Work.FeitSibley.CharQ.indQH_eq_indFun]
      change Work.Induction.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ) 1
        = (Nat.card h.D : ℂ) * (φ 1)
      rw [Work.Induction.indFun_apply_one, Work.FeitSibley.CharQ.pull_one,
        Work.FeitSibley.Coherence.index_subgroupOf_Q h]
    have h2 : (Work.CharCore.irrDeg χ : ℂ)
        = (Nat.card h.D : ℂ) * (Work.CharCore.irrDeg φ : ℂ) := by
      rw [← Work.CharCore.irrDeg_spec hχIrr, ← Work.CharCore.irrDeg_spec hφirr, h1]
    have h3 : ((Work.CharCore.irrDeg χ : ℕ) : ℂ)
        = ((Nat.card h.D * Work.CharCore.irrDeg φ : ℕ) : ℂ) := by
      rw [h2]; push_cast; ring
    exact_mod_cast h3
  exact ⟨lam, θ, hlam, hθ, by rw [hχeq, hφeq], hlamtriv, hlam1, by rw [hdegχ, hφθ]⟩

/-- **The `prodChar` structure of `𝒳`.**  A character `χ ∈ 𝒮 ∖ 𝒮(Z)` is induced from
`prodChar λ θ` with `θ` non-trivial at an element of `Z`; in particular
`irrDeg χ = |D| · irrDeg λ · irrDeg θ`, and `irrDeg θ = p^k` (`θ` lies in the odd `p`-group `Q₁`). -/
theorem exists_prodChar_deg_of_mem_sdiff_FSZ {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {χ : ↥h.H → ℂ}
    (hχ : χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h))) :
    ∃ (lam : ↥h.S → ℂ) (θ : ↥h.Q1 → ℂ), lam ∈ Work.CharCore.Irr ↥h.S ∧
      θ ∈ Work.CharCore.Irr ↥h.Q1 ∧ χ = h.indQH (h.prodChar lam θ) ∧
      (∃ z : ↥h.Q1, (z : G) ∈ FSZ h ∧ θ z ≠ θ 1) ∧
      Work.CharCore.irrDeg χ = Nat.card h.D * Work.CharCore.irrDeg lam *
        Work.CharCore.irrDeg θ := by
  classical
  obtain ⟨hχS, hχZ⟩ := Finset.mem_sdiff.mp hχ
  obtain ⟨φ, hφirr, hφw, hχeq⟩ := (Work.FeitSibley.CharQ.scriptS_eq_image h).mp hχS
  obtain ⟨lam, hlam, θ, hθ, hφeq⟩ := Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr h hφirr
  have hθne : θ ≠ fun _ : ↥h.Q1 => 1 :=
    Work.FeitSibley.CharQ.prodChar_Q1_component_ne_trivial h hlam
      (by rw [← hφeq]; exact hφw)
  have hZQ1 : FSZ h ≤ h.Q1 := FSZ_le_Q1' h
  have hZn : h.H ≤ Subgroup.normalizer (FSZ h : Set G) := FSZ_normal_in_H' h
  -- `θ` is non-trivial on `Z`, else `χ` would lie in `𝒮(Z)`
  have hθZ : ∃ z : ↥h.Q1, (z : G) ∈ FSZ h ∧ θ z ≠ θ 1 := by
    by_contra hcon
    push_neg at hcon
    have hiff := (Work.FeitSibley.Coherence.mem_scriptSR_prodChar_iff h hlam hθ hθne hZQ1 hZn)
    have hmem' : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h) := by
      rw [hχeq, hφeq]
      exact hiff.mpr hcon
    exact hχZ hmem'
  -- the degree
  have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχS).1
  have hprodIrr : h.prodChar lam θ ∈ Work.CharCore.Irr ↥h.Q :=
    Work.FeitSibley.CharQ.prodChar_mem_Irr h hlam hθ
  have hdeg : Work.CharCore.irrDeg χ = Nat.card h.D * Work.CharCore.irrDeg lam *
      Work.CharCore.irrDeg θ := by
    have h1 : χ 1 = (Nat.card h.D : ℂ) * (lam 1 * θ 1) := by
      rw [hχeq, hφeq, Work.FeitSibley.CharQ.indQH_eq_indFun]
      change Work.Induction.indFun (h.Q.subgroupOf h.H)
        (Work.FeitSibley.CharQ.pull h (h.prodChar lam θ)) 1
        = (Nat.card h.D : ℂ) * (lam 1 * θ 1)
      rw [Work.Induction.indFun_apply_one, Work.FeitSibley.CharQ.pull_one,
        Work.FeitSibley.Coherence.index_subgroupOf_Q h,
        Work.FeitSibley.FSData.prodChar_one]
    have h2 : (Work.CharCore.irrDeg χ : ℂ) = (Nat.card h.D : ℂ) *
        ((Work.CharCore.irrDeg lam : ℂ) * (Work.CharCore.irrDeg θ : ℂ)) := by
      rw [← Work.CharCore.irrDeg_spec hχIrr, ← Work.CharCore.irrDeg_spec hlam,
        ← Work.CharCore.irrDeg_spec hθ, h1]
    have h3 : ((Work.CharCore.irrDeg χ : ℕ) : ℂ)
        = ((Nat.card h.D * Work.CharCore.irrDeg lam * Work.CharCore.irrDeg θ : ℕ) : ℂ) := by
      rw [h2]; push_cast; ring
    exact_mod_cast h3
  exact ⟨lam, θ, hlam, hθ, by rw [hχeq, hφeq], hθZ, hdeg⟩

/-- If `θ ∈ Irr Q₁` is non-trivial at an element of `Q₁' = [Q₁,Q₁]` and `Q₁` is a `p`-group,
then `p ≤ irrDeg θ`.  Indeed `irrDeg θ` divides `|Q₁| = p^n` and is `≠ 1`: a degree-one `θ` is a
homomorphism into the abelian group `ℂˣ`, whence trivial on the derived subgroup
(`Subgroup.commutator_le`). -/
theorem p_le_irrDeg_of_nontrivial_on_commutator {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime) (hpg : IsPGroup p h.Q1)
    {θ : ↥h.Q1 → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥h.Q1)
    (hne : ∃ z : ↥h.Q1, (z : G) ∈ ⁅h.Q1, h.Q1⁆ ∧ θ z ≠ θ 1) :
    p ≤ Work.CharCore.irrDeg θ := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
  have hdvd : Work.CharCore.irrDeg θ ∣ p ^ n := by
    obtain ⟨d, hd1, hd2⟩ := Work.CharCore.irr_degree_dvd hθ
    have hdeg : Work.CharCore.irrDeg θ = d := by
      apply Nat.cast_injective (R := ℂ)
      rw [← Work.CharCore.irrDeg_spec hθ, hd1]
    rw [← hn, hdeg]
    exact hd2
  have hne1 : Work.CharCore.irrDeg θ ≠ 1 := by
    intro h1
    obtain ⟨z, hz, hzne⟩ := hne
    obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hθ).mp h1
    have hzmem : z ∈ commutator ↥h.Q1 := by
      rw [← Subgroup.map_subtype_commutator h.Q1] at hz
      obtain ⟨w, hw, hwe⟩ := hz
      exact (show z = w from Subtype.ext hwe.symm) ▸ hw
    have hker : commutator ↥h.Q1 ≤ MonoidHom.ker φ := by
      show ⁅(⊤ : Subgroup ↥h.Q1), (⊤ : Subgroup ↥h.Q1)⁆ ≤ MonoidHom.ker φ
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker]
      have hval : φ ⁅g₁, g₂⁆ = φ g₁ * φ g₂ * (φ g₁)⁻¹ * (φ g₂)⁻¹ := by
        rw [show ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ from rfl, map_mul, map_mul, map_mul,
          map_inv, map_inv]
      rw [hval]
      simp [mul_comm, mul_assoc, mul_left_comm]
    have hφz : φ z = 1 := hker hzmem
    have hz1 : θ z = 1 := by rw [hφ z, hφz]; simp
    have h11 : θ 1 = 1 := by rw [hφ 1, map_one]; simp
    exact hzne (by rw [hz1, h11])
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne1
  have hqeq : q = p := by
    have hqp : q ∣ p := hq.dvd_of_dvd_pow (hqdvd.trans hdvd)
    rcases hp.eq_one_or_self_of_dvd q hqp with h' | h'
    · exact absurd h' hq.ne_one
    · exact h'
  have hpq : p ∣ Work.CharCore.irrDeg θ := by rwa [← hqeq]
  exact Nat.le_of_dvd (Work.CharCore.irrDeg_pos hθ) hpq

/-- **The degree structure of `𝒳 = 𝒮∖𝒮(Z)`** (item 1 of the crux).  With `θ₁ ∈ Irr Q₁` of
minimal degree among the irreducible characters of `Q₁` non-trivial on `Z = FSZ h`
(`exists_irr_min_deg_not_triv_on_FSZ`), the character `x₀ = Ind_Q^H(prodChar 1 θ₁)` lies in `𝒳`
(`xi_mem_sdiff_FSZ`), has degree `|D|·irrDeg θ₁` with `2 ≤ irrDeg θ₁`, and its degree divides the
degree of every `x ∈ 𝒳` (`xi_dvd_irrDeg`). -/
theorem exists_min_deg_sdiff_FSZ {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {p : ℕ} (hp : p.Prime) (hpg : IsPGroup p h.Q1) (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) :
    ∃ x₀ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
      ∃ a : ℕ, 2 ≤ a ∧ x₀ 1 = (a : ℂ) * (Nat.card h.D : ℂ) ∧
        ∀ x ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)), ∃ k : ℤ, x 1 = (k : ℂ) * (x₀ 1) := by
  classical
  have hp2 : p ≠ 2 := fun h2 => h.Q1_not_two (h2 ▸ hpg)
  obtain ⟨θ₁, hθ₁, hθ₁Z, hθ₁min⟩ :=
    Work.FeitSibley.Coherence.exists_irr_min_deg_not_triv_on_FSZ h
      (FSZ_ne_bot' h hp hpg hab)
  let x₀ : ↥h.H → ℂ := h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)
  have hx₀mem : x₀ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) :=
    Work.FeitSibley.Coherence.xi_mem_sdiff_FSZ h hθ₁ hθ₁Z
  have hx₀Irr : x₀ ∈ Work.CharCore.Irr ↥h.H :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx₀mem).1).1
  have hx₀val : x₀ 1 = ((Work.CharCore.irrDeg θ₁ : ℕ) : ℂ) * (Nat.card h.D : ℂ) := by
    show (h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)) 1
      = ((Work.CharCore.irrDeg θ₁ : ℕ) : ℂ) * (Nat.card h.D : ℂ)
    rw [Work.FeitSibley.CharQ.indQH_eq_indFun]
    change Work.Induction.indFun (h.Q.subgroupOf h.H)
      (Work.FeitSibley.CharQ.pull h (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) θ₁)) 1
      = ((Work.CharCore.irrDeg θ₁ : ℕ) : ℂ) * (Nat.card h.D : ℂ)
    rw [Work.Induction.indFun_apply_one, Work.FeitSibley.CharQ.pull_one,
      Work.FeitSibley.Coherence.index_subgroupOf_Q h, Work.FeitSibley.FSData.prodChar_one,
      Work.CharCore.irrDeg_spec hθ₁]
    ring
  have h21 : 2 ≤ Work.CharCore.irrDeg θ₁ := by
    obtain ⟨z, hz, hzne⟩ := hθ₁Z
    have hFSZle : FSZ h ≤ ⁅h.Q1, h.Q1⁆ := inf_le_left
    have hpθ := p_le_irrDeg_of_nontrivial_on_commutator h hp hpg hθ₁ ⟨z, hFSZle hz, hzne⟩
    have hp3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd with h2 | hodd
      · exact absurd h2 hp2
      · have h2' := hp.two_le
        omega
    omega
  have hdiv : ∀ x ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)), ∃ k : ℤ, x 1 = (k : ℂ) * (x₀ 1) := by
    intro x hx
    obtain ⟨k, hk⟩ :=
      Work.FeitSibley.Coherence.xi_dvd_irrDeg h hp hpg hθ₁ hθ₁Z hθ₁min x hx
    have hxIrr : x ∈ Work.CharCore.Irr ↥h.H :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).1
    have hx₀deg : Work.CharCore.irrDeg x₀ = Nat.card h.D * Work.CharCore.irrDeg θ₁ := by
      have hv := hx₀val
      rw [Work.CharCore.irrDeg_spec hx₀Irr] at hv
      have h2 : ((Work.CharCore.irrDeg x₀ : ℕ) : ℂ)
          = ((Nat.card h.D * Work.CharCore.irrDeg θ₁ : ℕ) : ℂ) := by
        rw [hv, Nat.cast_mul]
        ring
      exact Nat.cast_injective h2
    refine ⟨(k : ℤ), ?_⟩
    rw [Work.CharCore.irrDeg_spec hxIrr, hk, hx₀deg, hx₀val]
    push_cast
    ring
  exact ⟨x₀, hx₀mem, Work.CharCore.irrDeg θ₁, h21, hx₀val, hdiv⟩

/-- **Item 2 of the crux: the key identity.**  For a coherent extension `ρ` of
`𝒴 = 𝒮(Q')`, a character `x₀ ∈ 𝒳` with `x₀ 1 = a·|D|` and `y₀, y ∈ 𝒴` with `y ≠ y₀`:

`⟨Ind_H^G(x₀ − a·y₀), ρ y − ρ y₀⟩ = a`.

Indeed `y − y₀ ∈ ℤ[𝒴]⁰`, so `ρ y − ρ y₀ = Ind(y − y₀)`; the isometry `Ind_H^G` on `ℤ[𝒮]⁰` moves
this to `⟨x₀ − a·y₀, y − y₀⟩`, and orthonormality of `𝒮` with `𝒳 ∩ 𝒴 = ∅` leaves `a`. -/
theorem cfInner_indLin_T_rho_sub {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {x₀ y₀ y : ↥h.H → ℂ}
    (hx₀ : x₀ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)))
    (hy₀ : y₀ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h))
    (hy : y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) (hyne : y ≠ y₀)
    {a : ℕ} (hx₀deg : x₀ 1 = (a : ℂ) * (Nat.card h.D : ℂ))
    {ρ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hρ0 : ∀ α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)),
      ρ α = Work.FeitSibley.indLin h.H α) :
    Work.Coherence.cfInner (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) (ρ y - ρ y₀)
      = (a : ℂ) := by
  classical
  have hx₀S : x₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := (Finset.mem_sdiff.mp hx₀).1
  have hy₀S : y₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hy₀
  have hyS : y ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hy
  have hy₀deg : y₀ 1 = (Nat.card h.D : ℂ) := scriptSR_Qcomm_deg h hy₀
  have hydeg : y 1 = (Nat.card h.D : ℂ) := scriptSR_Qcomm_deg h hy
  have hS : Work.Coherence.Orthonormal (Work.FeitSibley.scriptS h.H h.Q1) :=
    Work.Coherence.irr_orthonormal_finset
      (fun x hx => (Work.CharCore.mem_Irr_iff_coherence).mp (Finset.mem_filter.mp hx).1)
  have hXY : Disjoint (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h))
      (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) := by
    rw [Finset.disjoint_left]
    intro x hx hxy
    exact (Finset.mem_sdiff.mp hx).2 (scriptSR_subset_of_le h (FSQcomm_ge_FSZ h) hxy)
  have hmemY : y - y₀ ∈ Work.Coherence.ZSpan0
      (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) := by
    refine ⟨AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hy)
      (Work.Coherence.self_mem_zSpan hy₀), ?_⟩
    show (y - y₀) 1 = 0
    rw [Pi.sub_apply, hydeg, hy₀deg, sub_self]
  have hmemY' : y - y₀ ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1) :=
    Work.Coherence.zSpan0_mono (scriptSR_subset_scriptS h (FSQcomm h)) hmemY
  have hmemX : x₀ - (a : ℂ) • y₀ ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1) := by
    refine ⟨?_, ?_⟩
    · refine AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hx₀S) ?_
      have hcast : (a : ℂ) • y₀ = (a : ℤ) • y₀ := Int.cast_smul_eq_zsmul ℂ a y₀
      rw [hcast]
      exact AddSubgroup.zsmul_mem _ (Work.Coherence.self_mem_zSpan hy₀S) _
    · show (x₀ - (a : ℂ) • y₀) 1 = 0
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx₀deg, hy₀deg]
      ring
  have h1 : Work.Coherence.cfInner x₀ y = 0 := by
    rw [hS x₀ hx₀S y hyS]
    exact ite_eq_right (fun hc : x₀ = y => Finset.disjoint_left.mp hXY hx₀ (hc.symm ▸ hy))
  have h2 : Work.Coherence.cfInner x₀ y₀ = 0 := by
    rw [hS x₀ hx₀S y₀ hy₀S]
    exact ite_eq_right (fun hc : x₀ = y₀ => Finset.disjoint_left.mp hXY hx₀ (hc.symm ▸ hy₀))
  have h3 : Work.Coherence.cfInner y₀ y = 0 := by
    rw [hS y₀ hy₀S y hyS]
    exact ite_eq_right (fun hc : y₀ = y => hyne hc.symm)
  have h4 : Work.Coherence.cfInner y₀ y₀ = 1 := by
    rw [hS y₀ hy₀S y₀ hy₀S]
    exact ite_eq_left rfl
  have hρsub : ρ y - ρ y₀ = Work.FeitSibley.indLin h.H (y - y₀) := by
    rw [← map_sub, hρ0 (y - y₀) hmemY]
  have hiso := (Work.FeitSibley.CharQ.isometry_indLin h).inner_eq
    (x₀ - (a : ℂ) • y₀) hmemX (y - y₀) hmemY'
  rw [hρsub, hiso]
  simp only [Work.Coherence.cfInner_sub_left, Work.Coherence.cfInner_sub_right,
    Work.Coherence.cfInner_smul_left, h1, h2, h3, h4]
  ring

/-- **Item 2 of the crux: the norm identity.**  With `x₀ ∈ 𝒳` of degree `a·|D|` and
`y₀ ∈ 𝒴` of degree `|D|`, the character `T = Ind_H^G(x₀ − a·y₀)` has
`⟨T, T⟩ = 1 + a²`: the isometry on `ℤ[𝒮]⁰` reduces this to
`⟨x₀ − a·y₀, x₀ − a·y₀⟩`, and orthonormality of `𝒮` with `𝒳 ∩ 𝒴 = ∅` leaves
`1 − 0 − 0 + a²·1`. -/
theorem cfInner_indLin_T_self {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {x₀ : ↥h.H → ℂ}
    (hx₀ : x₀ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)))
    {y₀ : ↥h.H → ℂ} (hy₀ : y₀ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h))
    {a : ℕ} (hx₀deg : x₀ 1 = (a : ℂ) * (Nat.card h.D : ℂ)) :
    Work.Coherence.cfInner (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀))
      (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) = 1 + (a : ℂ) ^ 2 := by
  classical
  have hx₀S : x₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := (Finset.mem_sdiff.mp hx₀).1
  have hy₀S : y₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hy₀
  have hy₀deg : y₀ 1 = (Nat.card h.D : ℂ) := scriptSR_Qcomm_deg h hy₀
  have hS : Work.Coherence.Orthonormal (Work.FeitSibley.scriptS h.H h.Q1) :=
    Work.Coherence.irr_orthonormal_finset
      (fun x hx => (Work.CharCore.mem_Irr_iff_coherence).mp (Finset.mem_filter.mp hx).1)
  have hXY : Disjoint (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h))
      (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) := by
    rw [Finset.disjoint_left]
    intro x hx hxy
    exact (Finset.mem_sdiff.mp hx).2 (scriptSR_subset_of_le h (FSQcomm_ge_FSZ h) hxy)
  have hmemX : x₀ - (a : ℂ) • y₀ ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1) := by
    refine ⟨?_, ?_⟩
    · refine AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hx₀S) ?_
      have hcast : (a : ℂ) • y₀ = (a : ℤ) • y₀ := Int.cast_smul_eq_zsmul ℂ a y₀
      rw [hcast]
      exact AddSubgroup.zsmul_mem _ (Work.Coherence.self_mem_zSpan hy₀S) _
    · show (x₀ - (a : ℂ) • y₀) 1 = 0
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx₀deg, hy₀deg]
      ring
  have h1 : Work.Coherence.cfInner x₀ x₀ = 1 := by
    rw [hS x₀ hx₀S x₀ hx₀S]
    exact ite_eq_left rfl
  have h2 : Work.Coherence.cfInner x₀ y₀ = 0 := by
    rw [hS x₀ hx₀S y₀ hy₀S]
    exact ite_eq_right (fun hc : x₀ = y₀ => Finset.disjoint_left.mp hXY hx₀ (hc.symm ▸ hy₀))
  have h3 : Work.Coherence.cfInner y₀ x₀ = 0 := by
    rw [hS y₀ hy₀S x₀ hx₀S]
    exact ite_eq_right (fun hc : y₀ = x₀ => Finset.disjoint_left.mp hXY hx₀ (hc ▸ hy₀))
  have h4 : Work.Coherence.cfInner y₀ y₀ = 1 := by
    rw [hS y₀ hy₀S y₀ hy₀S]
    exact ite_eq_left rfl
  have hiso := (Work.FeitSibley.CharQ.isometry_indLin h).inner_eq
    (x₀ - (a : ℂ) • y₀) hmemX (x₀ - (a : ℂ) • y₀) hmemX
  rw [hiso]
  simp only [Work.Coherence.cfInner_sub_left, Work.Coherence.cfInner_sub_right,
    Work.Coherence.cfInner_smul_left, Work.Coherence.cfInner_smul_right, h1, h2, h3, h4,
    Complex.conj_natCast]
  ring

/-- The Feit-criterion bound of App. XII step (6) used to pass from `𝒳 ∩ 𝒮(S') ∪ 𝒴` to `𝒮(S')`. -/
theorem feitsibley_final_ineq {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hD : h.D ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1)
    (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥)
    {χ : ↥h.H → ℂ}
    (hχ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h))
    (hχS0 : χ ∉ (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
          Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h)
        ∪ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) :
    2 * Nat.card h.D * Work.CharCore.irrDeg χ <
      (∑ ξ ∈ ((Work.FeitSibley.scriptS h.H h.Q1 \
            Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
            Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h)
          ∪ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)),
        (Work.CharCore.irrDeg ξ) ^ 2) := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact absurd h2 hp2
    · have h2' := hp.two_le
      omega
  have hZQ1 : FSZ h ≤ h.Q1 := FSZ_le_Q1' h
  have hZn : h.H ≤ Subgroup.normalizer (FSZ h : Set G) := FSZ_normal_in_H' h
  have hZe : FSZ h ≠ ⊥ := FSZ_ne_bot' h hp hpg hab
  -- the decomposition of `χ`
  obtain ⟨lam, θ, hlam, hθ, hχeq, hlamtriv, hlam1, hdegχ⟩ :=
    exists_prodChar_of_mem_scriptSR_FSScomm h hχ
  have hχS : χ ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hχ
  have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχS).1
  have hχQ' : χ ∉ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h) := fun hmem =>
    hχS0 (Finset.mem_union.mpr (Or.inr hmem))
  -- (1) `θ` is non-trivial on `Q₁'`, else `χ` would lie in `𝒴`
  have hQ1'Q1 : ⁅h.Q1, h.Q1⁆ ≤ h.Q1 :=
    (Subgroup.commutator_le_sup h.Q1 h.Q1).trans (le_of_eq (sup_idem h.Q1))
  have hQ1'n : h.H ≤ Subgroup.normalizer (⁅h.Q1, h.Q1⁆ : Subgroup G) :=
    H_le_normalizer_commutator_Q1 h
  have hθne : ∃ z : ↥h.Q1, (z : G) ∈ ⁅h.Q1, h.Q1⁆ ∧ θ z ≠ θ 1 := by
    by_contra hcon
    push_neg at hcon
    have hφtriv : ∀ z : ↥h.Q, (z : G) ∈ ⁅h.Q1, h.Q1⁆ →
        h.prodChar lam θ z = h.prodChar lam θ 1 := by
      intro z hz
      rw [Work.FeitSibley.CharQ.prodChar_apply_of_mem_Q1 h lam θ z (hQ1'Q1 hz),
        Work.FeitSibley.FSData.prodChar_one]
      rw [(hcon ⟨(z : G), hQ1'Q1 hz⟩ hz)]
    have hχtriv : ∀ x : ↥h.H, (x : G) ∈ ⁅h.Q1, h.Q1⁆ → χ x = χ 1 := by
      intro x hx
      rw [hχeq]
      exact Work.FeitSibley.Coherence.indQH_apply_eq_one_of_triv_on_Z h
        (hQ1'Q1.trans h.Q1_le_Q) hQ1'n hφtriv hx
    have hFSSle : FSScomm h ≤ h.H := (FSScomm_le_S h).trans h.S_le_H
    have hQ1'le : ⁅h.Q1, h.Q1⁆ ≤ h.H := hQ1'Q1.trans h.Q1_le_H
    have hkerS' : (FSScomm h).subgroupOf h.H ≤ Work.CharCore.irrKer χ hχIrr := by
      intro z hz
      show z ∈ (Work.CharCore.irrKer χ hχIrr : Set ↥h.H)
      rw [Work.CharCore.coe_irrKer χ hχIrr, Work.CharCore.mem_charKernel]
      exact (mem_scriptSR_iff h (FSScomm h)).mp hχ |>.2 z (Subgroup.mem_subgroupOf.mp hz)
    have hker1 : (⁅h.Q1, h.Q1⁆).subgroupOf h.H ≤ Work.CharCore.irrKer χ hχIrr := by
      intro z hz
      show z ∈ (Work.CharCore.irrKer χ hχIrr : Set ↥h.H)
      rw [Work.CharCore.coe_irrKer χ hχIrr, Work.CharCore.mem_charKernel]
      exact hχtriv z (Subgroup.mem_subgroupOf.mp hz)
    have hkerQ' : (FSQcomm h).subgroupOf h.H ≤ Work.CharCore.irrKer χ hχIrr := by
      rw [FSQcomm_eq_sup, Subgroup.subgroupOf_sup hFSSle hQ1'le]
      exact sup_le hkerS' hker1
    refine hχQ' ((mem_scriptSR_iff h (FSQcomm h)).mpr ⟨hχS, fun x hx => ?_⟩)
    have hx' : x ∈ (FSQcomm h).subgroupOf h.H := Subgroup.mem_subgroupOf.mpr hx
    have hthis := hkerQ' hx'
    have h2 : x ∈ (Work.CharCore.irrKer χ hχIrr : Set ↥h.H) := hthis
    rw [Work.CharCore.coe_irrKer χ hχIrr, Work.CharCore.mem_charKernel] at h2
    exact h2
  -- (2) `3·|D| ≤ χ(1)`
  have hpθ : p ≤ Work.CharCore.irrDeg θ :=
    p_le_irrDeg_of_nontrivial_on_commutator h hp hpg hθ hθne
  have h3d : 3 * Nat.card h.D ≤ Work.CharCore.irrDeg χ := by
    rw [hdegχ]
    calc 3 * Nat.card h.D ≤ p * Nat.card h.D := Nat.mul_le_mul_right _ hp3
      _ ≤ Work.CharCore.irrDeg θ * Nat.card h.D := Nat.mul_le_mul_right _ hpθ
      _ = Nat.card h.D * Work.CharCore.irrDeg θ := by ring
  -- (3) `(𝒮∖𝒮(Z)) ∩ 𝒮(S') = 𝒮(S') ∖ 𝒮(S' ⊔ Z)`
  have hset : ((Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
        Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h))
      = Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ FSZ h) := by
    ext ξ
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hξS, hξZ⟩, hξS'⟩
      refine ⟨hξS', fun hmem => hξZ ?_⟩
      rw [mem_scriptSR_iff]
      refine ⟨hξS, fun x hx => ?_⟩
      exact (mem_scriptSR_iff h (FSScomm h ⊔ FSZ h)).mp hmem |>.2 x
        ((le_sup_right (a := FSScomm h) (b := FSZ h)) hx)
    · rintro ⟨hξS', hξZ'⟩
      have hξS := (mem_scriptSR_iff h (FSScomm h)).mp hξS'
      refine ⟨⟨hξS.1, fun hξZmem => hξZ' ?_⟩, hξS'⟩
      rw [mem_scriptSR_iff]
      refine ⟨hξS.1, fun x hx => ?_⟩
      have hξIrr : ξ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hξS.1).1
      have hA : (FSScomm h).subgroupOf h.H ≤ Work.CharCore.irrKer ξ hξIrr := by
        intro z hz
        show z ∈ (Work.CharCore.irrKer ξ hξIrr : Set ↥h.H)
        rw [Work.CharCore.coe_irrKer ξ hξIrr, Work.CharCore.mem_charKernel]
        exact hξS.2 z (Subgroup.mem_subgroupOf.mp hz)
      have hB : (FSZ h).subgroupOf h.H ≤ Work.CharCore.irrKer ξ hξIrr := by
        intro z hz
        show z ∈ (Work.CharCore.irrKer ξ hξIrr : Set ↥h.H)
        rw [Work.CharCore.coe_irrKer ξ hξIrr, Work.CharCore.mem_charKernel]
        exact (mem_scriptSR_iff h (FSZ h)).mp hξZmem |>.2 z (Subgroup.mem_subgroupOf.mp hz)
      have hx' : x ∈ (FSScomm h ⊔ FSZ h).subgroupOf h.H := Subgroup.mem_subgroupOf.mpr hx
      rw [Subgroup.subgroupOf_sup ((FSScomm_le_S h).trans h.S_le_H)
        (hZQ1.trans h.Q1_le_H)] at hx'
      have hthis := (sup_le hA hB) hx'
      have h2 : x ∈ (Work.CharCore.irrKer ξ hξIrr : Set ↥h.H) := hthis
      rw [Work.CharCore.coe_irrKer ξ hξIrr, Work.CharCore.mem_charKernel] at h2
      exact h2
  -- the two sums
  have hsumR : (∑ ξ ∈ ((Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
        Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h)), ((Work.CharCore.irrDeg ξ : ℝ)) ^ 2)
      = (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
        ((Nat.card h.Q1 : ℝ) - (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) := by
    have hreal := Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_sdiff_real h hZQ1 hZn
    rw [← hset] at hreal
    exact hreal
  have hZodd : Odd (Nat.card ↥(FSZ h)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
    have hdvd : Nat.card ↥(FSZ h) ∣ p ^ n := by
      rw [← hn]
      exact Subgroup.card_dvd_of_le hZQ1
    have hne0 : Nat.card ↥(FSZ h) ≠ 0 := by
      haveI : Nonempty ↥(FSZ h) := ⟨⟨1, (FSZ h).one_mem⟩⟩
      exact Nat.card_pos.ne'
    have hpow : Nat.card ↥(FSZ h) = p ^ (Nat.card ↥(FSZ h)).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hne0 (fun {q} hq hqdvd => by
        have hqp : q ∣ p := hq.dvd_of_dvd_pow (hqdvd.trans hdvd)
        rcases hp.eq_one_or_self_of_dvd q hqp with h' | h'
        · exact absurd h' hq.ne_one
        · exact h')
    rw [hpow]
    exact (hp.odd_of_ne_two hp2).pow
  have hZge : 2 * (Nat.card h.D : ℝ) + 1 ≤ (Nat.card ↥(FSZ h) : ℝ) := by
    have h0 := Work.FeitSibley.Coherence.two_mul_card_D_add_one_le_card_of_odd h (FSZ h)
      hZQ1 (h.D_le_H.trans hZn) hZe hZodd
    exact_mod_cast h0
  have hboundR : ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 ≤
      (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
        ((Nat.card h.Q1 : ℝ) - (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) := by
    have hcent : ⁅h.S, FSScomm h⁆ ≤ FSScomm h :=
      Subgroup.commutator_mono le_rfl
        ((Subgroup.commutator_le_sup h.S h.S).trans (le_of_eq (sup_idem h.S)))
    have h1 := Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR h (FSScomm h) (FSScomm h)
      (FSScomm_le_S h) (FSScomm_le_S h) le_rfl hcent hχ
    have hdvd : Nat.card ↥(FSScomm h) ∣ Nat.card h.S := Subgroup.card_dvd_of_le (FSScomm_le_S h)
    have hcard : Nat.card ↥((FSScomm h).subgroupOf h.S) = Nat.card ↥(FSScomm h) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (FSScomm_le_S h)).toEquiv
    have hidx' : ((FSScomm h).subgroupOf h.S).index = Nat.card h.S / Nat.card ↥(FSScomm h) := by
      have hmul := Subgroup.card_mul_index ((FSScomm h).subgroupOf h.S)
      rw [hcard] at hmul
      have hpos : 0 < Nat.card ↥(FSScomm h) := by
        haveI : Nonempty ↥(FSScomm h) := ⟨⟨1, (FSScomm h).one_mem⟩⟩
        exact Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [hmul, Nat.mul_div_cancel' hdvd]
    have hidx : (((FSScomm h).subgroupOf h.S).index : ℝ)
        = (Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ) := by
      rw [hidx', Nat.cast_div hdvd (by
        haveI : Nonempty ↥(FSScomm h) := ⟨⟨1, (FSScomm h).one_mem⟩⟩
        exact_mod_cast (Nat.card_pos (α := ↥(FSScomm h))).ne')]
    have hZpos : (0 : ℝ) < (Nat.card ↥(FSZ h) : ℝ) := by
      haveI : Nonempty ↥(FSZ h) := ⟨⟨1, (FSZ h).one_mem⟩⟩
      exact_mod_cast Nat.card_pos
    have hQZ : (Nat.card h.Q1 : ℝ) - (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)
        = ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) *
          ((Nat.card ↥(FSZ h) : ℝ) - 1) := by
      rw [mul_sub, mul_one, div_mul_cancel₀ _ hZpos.ne']
    have hbound' : ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 ≤
        (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
          (((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) *
            ((Nat.card ↥(FSZ h) : ℝ) - 1)) := by
      rw [hidx] at h1
      have hs : (0 : ℝ) ≤ (Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ) := by positivity
      have hqz : (0 : ℝ) ≤ (Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ) := by positivity
      have hd1 : (0 : ℝ) ≤ (Nat.card h.D : ℝ) := by positivity
      have hdZ : (Nat.card h.D : ℝ) ≤ (Nat.card ↥(FSZ h) : ℝ) - 1 := by linarith [hZge]
      have hsq : (Nat.card h.D : ℝ) ^ 2 ≤
          (Nat.card h.D : ℝ) * ((Nat.card ↥(FSZ h) : ℝ) - 1) := by nlinarith [hdZ, hd1]
      have hprod : (Nat.card h.D : ℝ) ^ 2 * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
            ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ))
          ≤ (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
            (((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) * ((Nat.card ↥(FSZ h) : ℝ) - 1)) := by
        have hstep1 : (Nat.card h.D : ℝ) ^ 2 * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ))
            ≤ (Nat.card h.D : ℝ) * ((Nat.card ↥(FSZ h) : ℝ) - 1) *
              ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) :=
          mul_le_mul_of_nonneg_right hsq hs
        have hstep2 : (Nat.card h.D : ℝ) ^ 2 * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
              ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ))
            ≤ (Nat.card h.D : ℝ) * ((Nat.card ↥(FSZ h) : ℝ) - 1) *
              ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
              ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep1 hqz
        calc (Nat.card h.D : ℝ) ^ 2 * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
                ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ))
            ≤ (Nat.card h.D : ℝ) * ((Nat.card ↥(FSZ h) : ℝ) - 1) *
                ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
                ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) := hstep2
          _ = (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
                (((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ)) * ((Nat.card ↥(FSZ h) : ℝ) - 1)) := by
              ring
      linarith [h1, hprod]
    rwa [← hQZ] at hbound'
  -- (4) the final chain
  have hmono : (∑ ξ ∈ ((Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
        Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h)), ((Work.CharCore.irrDeg ξ : ℝ)) ^ 2)
      ≤ (∑ ξ ∈ ((Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
          Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) ∪
          Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)), ((Work.CharCore.irrDeg ξ : ℝ)) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i _ _ => by positivity)
  have hmain : (2 : ℝ) * (Nat.card h.D : ℝ) * (Work.CharCore.irrDeg χ : ℝ)
      < ∑ ξ ∈ ((Work.FeitSibley.scriptS h.H h.Q1 \
            Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
            Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) ∪
            Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)), ((Work.CharCore.irrDeg ξ : ℝ)) ^ 2 := by
    have hχpos : (0 : ℝ) < (Work.CharCore.irrDeg χ : ℝ) := by
      exact_mod_cast Work.CharCore.irrDeg_pos hχIrr
    have h3dR : (3 : ℝ) * (Nat.card h.D : ℝ) ≤ (Work.CharCore.irrDeg χ : ℝ) := by
      exact_mod_cast h3d
    have hstep : (2 : ℝ) * (Nat.card h.D : ℝ) * (Work.CharCore.irrDeg χ : ℝ)
        ≤ (2 / 3) * (Work.CharCore.irrDeg χ : ℝ) ^ 2 := by
      nlinarith [h3dR, hχpos]
    have hχ2 : (Work.CharCore.irrDeg χ : ℝ) ^ 2
        ≤ ∑ ξ ∈ ((Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
          Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h)), ((Work.CharCore.irrDeg ξ : ℝ)) ^ 2 := by
      rw [hsumR]
      exact hboundR
    nlinarith [hstep, hχ2, hmono, hχpos]
  exact_mod_cast hmain

/-! ## The crux: Peterfalvi II, App. XII, steps (4)–(8) -/

/-- **Peterfalvi II, App. XII, steps (4)–(8).**  Given coherence of `𝒳 = 𝒮 ∖ 𝒮(Z)`, there are
coherence extensions `σ` (of `𝒳`) and `ρ` (of `𝒴 = 𝒮(Q')`, Milestone A) with mutually orthogonal
images and a cross relation `Ind(χ₁ - a·η₁) = σ χ₁ - a·ρ η₁`, where `χ₁` ranges over the minimal
degree in `𝒳` and `η₁` has degree `d = |D|`. -/
theorem two_block_relation {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hD : h.D ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1)
    (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) (hQhall : Nat.Coprime (Nat.card h.Q) h.Q.index)
    (hcoh : Work.Coherence.Coherent (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) (Work.FeitSibley.indLin h.H)) :
    ∃ (σ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)) (ρ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ))
      (x₀ : ↥h.H → ℂ) (y₀ : ↥h.H → ℂ) (a : ℕ),
      x₀ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∧
      y₀ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h) ∧
      2 ≤ a ∧ x₀ 1 = (a : ℂ) * (y₀ 1) ∧
      (∀ x ∈ (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        ∃ k : ℤ, x 1 = (k : ℂ) * (x₀ 1)) ∧
      (∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
        ∃ k : ℤ, y 1 = (k : ℂ) * (y₀ 1)) ∧
      (∀ α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        σ α = Work.FeitSibley.indLin h.H α) ∧
      Work.Coherence.IsometryOnAll (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) σ ∧
      (∀ x ∈ (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        Work.Coherence.IsVChar (σ x)) ∧
      (∀ α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)),
        ρ α = Work.FeitSibley.indLin h.H α) ∧
      Work.Coherence.IsometryOnAll (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) ρ ∧
      (∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h), Work.Coherence.IsVChar (ρ y)) ∧
      (∀ x ∈ (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
          Work.Coherence.cfInner (σ x) (ρ y) = 0) ∧
      Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀) = σ x₀ - (a : ℂ) • ρ y₀ := by
  classical
  -- ── step (4): the coherent extensions and their orthogonality ──
  obtain ⟨σ, ρ, hσ0, hσiso, hσV, hρ0, hρiso, hρV, horth⟩ :=
    exists_lift_pair_orthogonal h hD hp hp2 hpg hab hcoh
  -- ── the minimal-degree character of `𝒳` and a character of `𝒴` ──
  obtain ⟨x₀, hx₀X, a, ha2, hx₀deg, hdegX⟩ := exists_min_deg_sdiff_FSZ h hp hpg hab
  obtain ⟨y₀, hy₀Y⟩ := scriptSR_Qcomm_nonempty h (exists_nontrivial_linear_of_D_ne_bot h hD)
  have ha_ne : a ≠ 0 := by omega
  have hy₀deg : y₀ 1 = (Nat.card h.D : ℂ) := scriptSR_Qcomm_deg h hy₀Y
  have hdeg : x₀ 1 = (a : ℂ) * (y₀ 1) := by rw [hy₀deg, hx₀deg]
  have hdegY : ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
      ∃ k : ℤ, y 1 = (k : ℂ) * (y₀ 1) := by
    intro y hy
    exact ⟨1, by rw [scriptSR_Qcomm_deg h hy, hy₀deg]; ring⟩
  have hYort : Work.Coherence.Orthonormal (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) :=
    scriptSR_Qcomm_orthonormal h
  have hSort : Work.Coherence.Orthonormal (Work.FeitSibley.scriptS h.H h.Q1) :=
    Work.Coherence.irr_orthonormal_finset
      (fun x hx => (Work.CharCore.mem_Irr_iff_coherence).mp (Finset.mem_filter.mp hx).1)
  have hXort : Work.Coherence.Orthonormal (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) := hSort.mono Finset.sdiff_subset
  have hx₀S : x₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := (Finset.mem_sdiff.mp hx₀X).1
  have hy₀S : y₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hy₀Y
  have hXY : Disjoint (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h))
      (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) := by
    rw [Finset.disjoint_left]
    intro x hx hxy
    exact (Finset.mem_sdiff.mp hx).2 (scriptSR_subset_of_le h (FSQcomm_ge_FSZ h) hxy)
  -- ── step (6): the `λ`-decomposition of `T = Ind(x₀ - a·y₀)` ──
  let T : G → ℂ := Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)
  have hkey : ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h), y ≠ y₀ →
      Work.Coherence.cfInner T (ρ y) = Work.Coherence.cfInner T (ρ y₀) + (a : ℂ) := by
    intro y hy hyne
    have h1 := cfInner_indLin_T_rho_sub h hx₀X hy₀Y hy hyne hx₀deg hρ0
    rw [Work.Coherence.cfInner_sub_right] at h1
    exact (sub_eq_iff_eq_add.mp h1).trans (add_comm _ _)
  obtain ⟨c, hc⟩ := exists_lambda_T_rho h hx₀X hy₀Y hx₀deg hρV hkey
  have hρ1 : Work.Coherence.cfInner (ρ y₀) (ρ y₀) = 1 := by
    rw [hρiso.inner_eq y₀ (Work.Coherence.self_mem_zSpan hy₀Y) y₀
      (Work.Coherence.self_mem_zSpan hy₀Y)]
    exact hYort.cfInner_self hy₀Y
  -- ── step (8): `a ∣ λ` ──
  have hadvd : (a : ℤ) ∣ c :=
    a_dvd_lambda_two_block h hp hp2 hpg hab hQhall hx₀X hy₀Y ha_ne hx₀deg hdegX hσ0 horth
      (hρV y₀ hy₀Y) hρ1 hc
  -- ── the norm computation of step (6) ──
  have hTnorm : Work.Coherence.cfInner T T = 1 + (a : ℂ) ^ 2 :=
    cfInner_indLin_T_self h hx₀X hy₀Y hx₀deg
  have hcard2 : 2 ≤ (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)).card :=
    two_le_card_scriptSR_Qcomm h hp hpg hab
  have hTV : Work.Coherence.IsVChar T := by
    have h1 : Work.Coherence.IsVChar (Work.FeitSibley.indLin h.H x₀) :=
      isVChar_indLin_scriptS h hx₀S
    have h2 : Work.Coherence.IsVChar (Work.FeitSibley.indLin h.H y₀) :=
      isVChar_indLin_scriptS h hy₀S
    have h3 : T = Work.FeitSibley.indLin h.H x₀
        - (a : ℤ) • Work.FeitSibley.indLin h.H y₀ := by
      show Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀) = _
      have hcast : (a : ℂ) • y₀ = (a : ℤ) • y₀ := by
        conv_lhs => rw [← Int.cast_natCast (R := ℂ) a]
        rw [Int.cast_smul_eq_zsmul]
      rw [hcast, map_sub, map_zsmul]
    rw [h3]
    exact h1.sub (h2.zsmul (a : ℤ))
  have hdich : c = 0 ∨ (c = (a : ℤ) ∧
      (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)).card = 2) :=
    two_block_norm_dichotomy h hTV hρiso hy₀Y ha2 hadvd hTnorm hc hcard2
  -- ── reduce to the case `c = 0`, swapping the two elements of `𝒴` when `|𝒴| = 2` ──
  have hP : ∃ (ρ' : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)) (c' : ℤ),
      (∀ α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)),
        ρ' α = Work.FeitSibley.indLin h.H α) ∧
      Work.Coherence.IsometryOnAll (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) ρ' ∧
      (∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h), Work.Coherence.IsVChar (ρ' y)) ∧
      (∀ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
          Work.Coherence.cfInner (σ χ) (ρ' y) = 0) ∧
      (c' = 0 ∧
      ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
        Work.Coherence.cfInner T (ρ' y) = if y = y₀ then (c' : ℂ) - (a : ℂ) else (c' : ℂ)) := by
    rcases hdich with hc0 | ⟨hca, hcardeq⟩
    · exact ⟨ρ, c, hρ0, hρiso, hρV, horth, hc0, hc⟩
    · obtain ⟨p, q, hpq, hsum⟩ := Finset.card_eq_two.mp hcardeq
      have hY2 : ∃ y₂, y₂ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h) ∧ y₂ ≠ y₀ ∧
          (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h) = {y₀, y₂}) := by
        have hy₀pair : y₀ ∈ ({p, q} : Finset (↥h.H → ℂ)) := hsum ▸ hy₀Y
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy₀pair
        rcases hy₀pair with h | h
        · exact ⟨q, by rw [hsum]; simp, fun hc2 => hpq (h.symm.trans hc2.symm),
            by rw [hsum, h]⟩
        · exact ⟨p, by rw [hsum]; simp, fun hc2 => hpq (hc2.trans h),
            by rw [hsum, h, Finset.pair_comm]⟩
      obtain ⟨y₂, hy₂Y, hy₂ne, hYsum⟩ := hY2
      have hcoverY : ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
          y = y₀ ∨ y = y₂ := by
        intro y hy
        rw [hYsum] at hy
        simpa using hy
      have hdegY2 : y₀ 1 = y₂ 1 := by
        rw [scriptSR_Qcomm_deg h hy₀Y, scriptSR_Qcomm_deg h hy₂Y]
      have hy₀0 : y₀ 1 ≠ 0 := by
        rw [hy₀deg]
        exact_mod_cast Nat.card_pos.ne'
      obtain ⟨ρ', hρ'0, hρ'iso, hρ'V, hρ'y₀, hρ'y₂⟩ :=
        swap_negate_lift h hYort hρ0 hρiso hρV hy₀Y hy₂Y (fun hc2 => hy₂ne hc2.symm)
          hcoverY hdegY2 hy₀0
      refine ⟨ρ', 0, hρ'0, hρ'iso, hρ'V, ?_, rfl, ?_⟩
      · intro χ hχ y hy
        rcases hcoverY y hy with hyy | hyy
        · subst y
          rw [hρ'y₀, Work.Coherence.cfInner_neg_right, horth χ hχ y₂ hy₂Y, neg_zero]
        · subst y
          rw [hρ'y₂, Work.Coherence.cfInner_neg_right, horth χ hχ y₀ hy₀Y, neg_zero]
      · intro y hy
        rcases hcoverY y hy with hyy | hyy
        · subst y
          rw [hρ'y₀, Work.Coherence.cfInner_neg_right, hc y₂ hy₂Y]
          rw [ite_eq_right (fun hc2 : y₂ = y₀ => hy₂ne hc2), ite_eq_left rfl, hca]
          push_cast
          ring
        · subst y
          rw [hρ'y₂, Work.Coherence.cfInner_neg_right, hc y₀ hy₀Y, ite_eq_left rfl, hca]
          rw [ite_eq_right (fun hc2 : y₂ = y₀ => hy₂ne hc2)]
          push_cast
          ring
  obtain ⟨ρ', c', hρ'0, hρ'iso, hρ'V, horth', hc'0, hc'form⟩ := hP
  -- ── the vector `vv = T + a·ρ' y₀` (orthogonal to `ρ'𝒴`, of norm `1`) ──
  let vv : G → ℂ := T + (a : ℂ) • ρ' y₀
  have hvvorth : ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h),
      Work.Coherence.cfInner vv (ρ' y) = 0 := by
    intro y hy
    show Work.Coherence.cfInner (T + (a : ℂ) • ρ' y₀) (ρ' y) = 0
    rw [Work.Coherence.cfInner_add_left, Work.Coherence.cfInner_smul_left,
      hc'form y hy, hρ'iso.inner_eq y₀ (Work.Coherence.self_mem_zSpan hy₀Y) y
        (Work.Coherence.self_mem_zSpan hy), hYort y₀ hy₀Y y hy]
    by_cases hyy : y = y₀
    · rw [if_pos hyy, if_pos hyy.symm, hc'0]
      norm_num
    · rw [if_neg hyy, if_neg (fun hc2 : y₀ = y => hyy hc2.symm), hc'0]
      ring
  have hvvV : Work.Coherence.IsVChar vv := by
    show Work.Coherence.IsVChar (T + (a : ℂ) • ρ' y₀)
    refine hTV.add ?_
    have h1 := (hρ'V y₀ hy₀Y).zsmul (a : ℤ)
    have hcast : (a : ℂ) • ρ' y₀ = (a : ℤ) • ρ' y₀ := by
      conv_lhs => rw [← Int.cast_natCast (R := ℂ) a]
      rw [Int.cast_smul_eq_zsmul]
    rwa [← hcast] at h1
  have hvv1 : Work.Coherence.cfInner vv vv = 1 := by
    show Work.Coherence.cfInner (T + (a : ℂ) • ρ' y₀) (T + (a : ℂ) • ρ' y₀) = 1
    have hA : Work.Coherence.cfInner T T = 1 + (a : ℂ) ^ 2 := hTnorm
    have h0 : Work.Coherence.cfInner T (ρ' y₀) = 0 - (a : ℂ) := by
      rw [hc'form y₀ hy₀Y, hc'0, ite_eq_left rfl]
      push_cast
      ring
    have hB : Work.Coherence.cfInner T ((a : ℂ) • ρ' y₀) = (a : ℂ) * (0 - (a : ℂ)) := by
      rw [Work.Coherence.cfInner_smul_right, h0, Complex.conj_natCast]
    have hC : Work.Coherence.cfInner ((a : ℂ) • ρ' y₀) T = (a : ℂ) * (0 - (a : ℂ)) := by
      rw [Work.Coherence.cfInner_smul_left, Work.Coherence.cfInner_conj_symm, h0]
      rw [map_sub, map_zero, Complex.conj_natCast]
    have hD : Work.Coherence.cfInner ((a : ℂ) • ρ' y₀) ((a : ℂ) • ρ' y₀)
        = (a : ℂ) * (a : ℂ) * 1 := by
      rw [Work.Coherence.cfInner_smul_left, Work.Coherence.cfInner_smul_right,
        hρ'iso.inner_eq y₀ (Work.Coherence.self_mem_zSpan hy₀Y) y₀
          (Work.Coherence.self_mem_zSpan hy₀Y), hYort.cfInner_self hy₀Y,
        Complex.conj_natCast]
      ring
    rw [Work.Coherence.cfInner_add_left, Work.Coherence.cfInner_add_right,
      Work.Coherence.cfInner_add_right, hA, hB, hC, hD]
    ring
  have hTrel : T = vv - (a : ℂ) • ρ' y₀ := by
    show T = (T + (a : ℂ) • ρ' y₀) - (a : ℂ) • ρ' y₀
    abel
  -- ── the `-1` relation of step (6), for every `χ ≠ x₀` in `𝒳` ──
  have hrelgen : ∀ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)), χ ≠ x₀ →
      ∃ k : ℤ, 1 ≤ k ∧ χ 1 = (k : ℂ) * (x₀ 1) ∧
        Work.Coherence.cfInner vv (σ χ) - (k : ℂ) * Work.Coherence.cfInner vv (σ x₀)
          = -(k : ℂ) := by
    intro χ hχ hχne
    have hχS : χ ∈ Work.FeitSibley.scriptS h.H h.Q1 := (Finset.mem_sdiff.mp hχ).1
    have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχS).1
    have hx₀Irr : x₀ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hx₀S).1
    obtain ⟨k, hk⟩ := hdegX χ hχ
    have hk1 : 1 ≤ k := by
      have hk' : ((Work.CharCore.irrDeg χ : ℕ) : ℤ) = k * ((Work.CharCore.irrDeg x₀ : ℕ) : ℤ) := by
        have h := hk
        rw [Work.CharCore.irrDeg_spec hχIrr, Work.CharCore.irrDeg_spec hx₀Irr] at h
        exact_mod_cast h
      have h4 : (1 : ℤ) ≤ ((Work.CharCore.irrDeg x₀ : ℕ) : ℤ) := by
        exact_mod_cast Work.CharCore.irrDeg_pos hx₀Irr
      have h5 : (0 : ℤ) < ((Work.CharCore.irrDeg χ : ℕ) : ℤ) := by
        exact_mod_cast Work.CharCore.irrDeg_pos hχIrr
      nlinarith [hk', h4, h5]
    refine ⟨k, hk1, hk, ?_⟩
    have hmem1 : χ - (k : ℂ) • x₀ ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) := by
      refine ⟨?_, ?_⟩
      · refine AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hχ) ?_
        have hcast : (k : ℂ) • x₀ = (k : ℤ) • x₀ := Int.cast_smul_eq_zsmul ℂ k x₀
        rw [hcast]
        exact AddSubgroup.zsmul_mem _ (Work.Coherence.self_mem_zSpan hx₀X) _
      · show (χ - (k : ℂ) • x₀) 1 = 0
        rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hk, sub_self]
    have hmem2 : x₀ - (a : ℂ) • y₀ ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1) := by
      refine ⟨?_, ?_⟩
      · refine AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hx₀S) ?_
        have hcast : (a : ℂ) • y₀ = (a : ℤ) • y₀ := Int.cast_smul_eq_zsmul ℂ a y₀
        rw [hcast]
        exact AddSubgroup.zsmul_mem _ (Work.Coherence.self_mem_zSpan hy₀S) _
      · show (x₀ - (a : ℂ) • y₀) 1 = 0
        rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx₀deg, hy₀deg]
        ring
    have hχy₀ : χ ≠ y₀ := fun hc2 => Finset.disjoint_left.mp hXY hχ (hc2 ▸ hy₀Y)
    have hx₀y₀ : x₀ ≠ y₀ := fun hc2 => Finset.disjoint_left.mp hXY hx₀X (hc2 ▸ hy₀Y)
    have hiso := (Work.FeitSibley.CharQ.isometry_indLin h).inner_eq (χ - (k : ℂ) • x₀)
      (Work.Coherence.zSpan0_mono Finset.sdiff_subset hmem1)
      (x₀ - (a : ℂ) • y₀) hmem2
    have hval : Work.Coherence.cfInner (χ - (k : ℂ) • x₀) (x₀ - (a : ℂ) • y₀) = -(k : ℂ) := by
      have hA : Work.Coherence.cfInner χ x₀ = 0 := hSort.cfInner_eq_zero hχS hx₀S hχne
      have hB : Work.Coherence.cfInner χ y₀ = 0 := hSort.cfInner_eq_zero hχS hy₀S hχy₀
      have hC : Work.Coherence.cfInner x₀ x₀ = 1 := hSort.cfInner_self hx₀S
      have hD : Work.Coherence.cfInner x₀ y₀ = 0 := hSort.cfInner_eq_zero hx₀S hy₀S hx₀y₀
      rw [Work.Coherence.cfInner_sub_left, Work.Coherence.cfInner_smul_left,
        Work.Coherence.cfInner_sub_right, Work.Coherence.cfInner_sub_right,
        Work.Coherence.cfInner_smul_right, Work.Coherence.cfInner_smul_right,
        hA, hB, hC, hD, Complex.conj_natCast]
      ring
    rw [hval] at hiso
    have hσlin : σ (χ - (k : ℂ) • x₀) = σ χ - (k : ℂ) • σ x₀ := by
      rw [map_sub, Int.cast_smul_eq_zsmul ℂ k x₀, map_zsmul,
        ← Int.cast_smul_eq_zsmul ℂ k (σ x₀)]
    have hρ'σ : ∀ χ' ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)),
        Work.Coherence.cfInner (ρ' y₀) (σ χ') = 0 := by
      intro χ' hχ'
      rw [Work.Coherence.cfInner_conj_symm, horth' χ' hχ' y₀ hy₀Y, map_zero]
    have hkcast : (starRingEnd ℂ) ((k : ℤ) : ℂ) = (k : ℂ) := map_intCast (starRingEnd ℂ) k
    have hiso' : Work.Coherence.cfInner T
        (Work.FeitSibley.indLin h.H (χ - (k : ℂ) • x₀)) = -(k : ℂ) := by
      rw [Work.Coherence.cfInner_conj_symm, hiso, map_neg, map_intCast]
    have h1 : Work.Coherence.cfInner T (σ χ - (k : ℂ) • σ x₀) = -(k : ℂ) := by
      rw [← hσlin, hσ0 (χ - (k : ℂ) • x₀) hmem1]
      exact hiso'
    have hrel' : Work.Coherence.cfInner vv (σ χ) - (k : ℂ) * Work.Coherence.cfInner vv (σ x₀)
        = -(k : ℂ) := by
      have h := h1
      rw [hTrel, Work.Coherence.cfInner_sub_left, Work.Coherence.cfInner_smul_left,
        Work.Coherence.cfInner_sub_right, Work.Coherence.cfInner_sub_right,
        Work.Coherence.cfInner_smul_right, Work.Coherence.cfInner_smul_right,
        hρ'σ χ hχ, hρ'σ x₀ hx₀X, hkcast] at h
      simpa using h
    exact hrel'
  -- ── the dichotomy for `vv` against the images of `𝒳` ──
  have hdich2 : ∀ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)), χ ≠ x₀ →
      vv = σ x₀ ∨ (χ 1 = x₀ 1 ∧ vv = -σ χ) := by
    intro χ hχ hχne
    have hχS : χ ∈ Work.FeitSibley.scriptS h.H h.Q1 := (Finset.mem_sdiff.mp hχ).1
    obtain ⟨k, hk1, hk, hrel⟩ := hrelgen χ hχ hχne
    have hx₀σ1 : Work.Coherence.cfInner (σ x₀) (σ x₀) = 1 := by
      rw [hσiso.inner_eq x₀ (Work.Coherence.self_mem_zSpan hx₀X) x₀
        (Work.Coherence.self_mem_zSpan hx₀X)]
      exact hSort.cfInner_self hx₀S
    have hχσ1 : Work.Coherence.cfInner (σ χ) (σ χ) = 1 := by
      rw [hσiso.inner_eq χ (Work.Coherence.self_mem_zSpan hχ) χ
        (Work.Coherence.self_mem_zSpan hχ)]
      exact hSort.cfInner_self hχS
    have h12 : Work.Coherence.cfInner (σ x₀) (σ χ) = 0 := by
      rw [hσiso.inner_eq x₀ (Work.Coherence.self_mem_zSpan hx₀X) χ
        (Work.Coherence.self_mem_zSpan hχ)]
      exact hSort.cfInner_eq_zero hx₀S hχS (fun hc2 => hχne hc2.symm)
    rcases Work.Coherence.vchar_relation_dichotomy hvvV hvv1 (hσV x₀ hx₀X) hx₀σ1
      (hσV χ hχ) hχσ1 h12 hk1 hrel with h | ⟨hk1', h⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, h⟩
      rw [hk1'] at hk
      simpa using hk
  -- ── case analysis ──
  by_cases hvs : vv = σ x₀
  · refine ⟨σ, ρ', x₀, y₀, a, hx₀X, hy₀Y, ha2, hdeg, hdegX, hdegY, hσ0, hσiso, hσV,
      hρ'0, hρ'iso, hρ'V, horth', ?_⟩
    rw [hvs] at hTrel
    exact hTrel
  · obtain ⟨χ₂, hχ₂X, hχ₂ne⟩ : ∃ χ₂ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)), χ₂ ≠ x₀ := by
      have hlt : 1 < (Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)).card := by
        have := two_le_card_sdiff_FSZ h hp hpg hab
        omega
      obtain ⟨p, hp', q, hq', hpq⟩ := Finset.one_lt_card.mp hlt
      rcases eq_or_ne p x₀ with hh | hh
      · exact ⟨q, hq', fun hc2 => hpq (hh.trans hc2.symm)⟩
      · exact ⟨p, hp', hh⟩
    have hχ₂S : χ₂ ∈ Work.FeitSibley.scriptS h.H h.Q1 := (Finset.mem_sdiff.mp hχ₂X).1
    rcases hdich2 χ₂ hχ₂X hχ₂ne with hbad | ⟨hdeg₂', hgood⟩
    · exact absurd hbad hvs
    · have hcover : ∀ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
            Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)), χ = x₀ ∨ χ = χ₂ := by
        intro χ hχ
        by_cases hχx : χ = x₀
        · exact Or.inl hχx
        · rcases hdich2 χ hχ hχx with h1 | ⟨-, h1⟩
          · exact absurd h1 hvs
          · refine Or.inr ?_
            by_contra hne
            have hsum2 : σ χ = σ χ₂ := by rw [← neg_inj]; rw [← h1, ← hgood]
            have hinner : Work.Coherence.cfInner (σ χ) (σ χ₂)
                = Work.Coherence.cfInner χ χ₂ :=
              hσiso.inner_eq χ (Work.Coherence.self_mem_zSpan hχ) χ₂
                (Work.Coherence.self_mem_zSpan hχ₂X)
            have hone : Work.Coherence.cfInner (σ χ) (σ χ₂) = 1 := by
              rw [← hsum2, hσiso.inner_eq χ (Work.Coherence.self_mem_zSpan hχ) χ
                (Work.Coherence.self_mem_zSpan hχ)]
              exact hSort.cfInner_self ((Finset.mem_sdiff.mp hχ).1)
            rw [hinner, hSort.cfInner_eq_zero ((Finset.mem_sdiff.mp hχ).1) hχ₂S hne] at hone
            exact one_ne_zero hone.symm
      have hne₂ : x₀ ≠ χ₂ := fun hc2 => hχ₂ne hc2.symm
      have hdeg₂ : x₀ 1 = χ₂ 1 := hdeg₂'.symm
      have hx₀0 : x₀ 1 ≠ 0 := by
        rw [hx₀deg]
        exact mul_ne_zero (by exact_mod_cast ha_ne) (by exact_mod_cast Nat.card_pos.ne')
      obtain ⟨σ', hσ'0, hσ'iso, hσ'V, hσ'x₀, hσ'x₂⟩ :=
        swap_negate_lift h hXort hσ0 hσiso hσV hx₀X hχ₂X hne₂ hcover hdeg₂ hx₀0
      have hσ'x₀' : σ' x₀ = vv := by rw [hσ'x₀, hgood]
      refine ⟨σ', ρ', x₀, y₀, a, hx₀X, hy₀Y, ha2, hdeg, hdegX, hdegY, hσ'0, hσ'iso, hσ'V,
        hρ'0, hρ'iso, hρ'V, ?_, ?_⟩
      · intro χ hχ y hy
        rcases hcover χ hχ with h | h
        · rw [h, hσ'x₀, Work.Coherence.cfInner_neg_left, horth' χ₂ hχ₂X y hy, neg_zero]
        · rw [h, hσ'x₂, Work.Coherence.cfInner_neg_left, horth' x₀ hx₀X y hy, neg_zero]
      · rw [hσ'x₀']
        exact hTrel

/-! ## The main theorem -/

theorem coherent_scriptSR_of_pgroup {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hD : h.D ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1)
    (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) (hQhall : Nat.Coprime (Nat.card h.Q) h.Q.index)
    (hcoh : Work.Coherence.Coherent (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) (Work.FeitSibley.indLin h.H)) :
    Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h))
      (Work.FeitSibley.indLin h.H) := by
  classical
  -- The two-block argument (steps (4)–(8)) provides the coherent extensions `σ`, `ρ` and the
  -- cross relation; `coherent_union_two_blocks` then makes `𝒳 ∪ 𝒴` coherent.
  obtain ⟨σ, ρ, x₀, y₀, a, hx₀X, hy₀Y, ha2, hdeg, hdegX, hdegY, hσ0, hσiso, hσV, hρ0, hρiso,
    hρV, horth, hrel⟩ := two_block_relation h hD hp hp2 hpg hab hQhall hcoh
  have hXY : Disjoint (Work.FeitSibley.scriptS h.H h.Q1 \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h))
      (Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) := by
    rw [Finset.disjoint_left]
    intro x hx hxy
    exact (Finset.mem_sdiff.mp hx).2 (scriptSR_subset_of_le h (FSQcomm_ge_FSZ h) hxy)
  have hS : Work.Coherence.Orthonormal (Work.FeitSibley.scriptS h.H h.Q1) :=
    Work.Coherence.irr_orthonormal_finset
      (fun x hx => (Work.CharCore.mem_Irr_iff_coherence).mp (Finset.mem_filter.mp hx).1)
  have hcohU : Work.Coherence.Coherent
      ((Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∪
        Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) (Work.FeitSibley.indLin h.H) :=
    coherent_union_two_blocks hS (Finset.sdiff_subset) (scriptSR_subset_scriptS h _) hXY
      hσ0 hσiso hσV hρ0 hρiso hρV horth hx₀X hy₀Y hdegX hdegY hdeg hrel
  -- Restrict to the part of `𝒳` lying in the target `𝒯 = 𝒮(S')`.
  have hS0 : Work.Coherence.Coherent
      (((Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
          Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h)) ∪
        Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) (Work.FeitSibley.indLin h.H) :=
    Work.Coherence.coherent_mono (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_inter] at hx ⊢
      rcases hx with ⟨hx1, _⟩ | hx2
      · exact Or.inl hx1
      · exact Or.inr hx2) hcohU
  -- Feit's criterion (App. XII step (6)) extends coherence to `𝒯 = 𝒮(S')`.
  refine coherent_of_feit_step ?_ ?_ ?_ ?_ hS0 ?_
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_inter] at hx
    rcases hx with ⟨hx1, hx2⟩ | hx2
    · exact hx2
    · exact scriptSR_subset_of_le h (FSScomm_le_FSQcomm h) hx2
  · intro x hx
    exact (Finset.mem_filter.mp (scriptSR_subset_scriptS h _ hx)).1
  · exact ⟨fun α hα β hβ =>
      (Work.FeitSibley.CharQ.isometry_indLin h).inner_eq α
        (Work.Coherence.zSpan0_mono (scriptSR_subset_scriptS h _) hα) β
        (Work.Coherence.zSpan0_mono (scriptSR_subset_scriptS h _) hβ)⟩
  · intro α hα
    exact isVChar_indLin_zSpan0_scriptS h
      (Work.Coherence.zSpan0_mono (scriptSR_subset_scriptS h _) hα)
  · intro χ hχT hχS0 hineq
    -- The inequality of Feit's criterion contradicts `feitsibley_final_ineq`
    -- (test `ψ := y₀ ∈ 𝒴 ⊆ S₀`).
    have hbound := feitsibley_final_ineq h hD hp hp2 hpg hab hχT hχS0
    have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H :=
      (Finset.mem_filter.mp (scriptSR_subset_scriptS h _ hχT)).1
    have hy₀Irr : y₀ ∈ Work.CharCore.Irr ↥h.H :=
      (Finset.mem_filter.mp (scriptSR_subset_scriptS h _ hy₀Y)).1
    obtain ⟨_lam, θ, _hlam, _hθ, _hχeq, _hlamtriv, _hlam1, hdegχ⟩ :=
      exists_prodChar_of_mem_scriptSR_FSScomm h hχT
    have hy₀deg : y₀ 1 = (Nat.card h.D : ℂ) := scriptSR_Qcomm_deg h hy₀Y
    have hy₀S0 : y₀ ∈ ((Work.FeitSibley.scriptS h.H h.Q1 \
          Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)) ∩
          Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) ∪
          Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)) :=
      Finset.mem_union.mpr (Or.inr hy₀Y)
    have hy₀irrDeg : Work.CharCore.irrDeg y₀ = Nat.card h.D := by
      have h1 : ((Work.CharCore.irrDeg y₀ : ℕ) : ℂ) = ((Nat.card h.D : ℕ) : ℂ) := by
        rw [← Work.CharCore.irrDeg_spec hy₀Irr, hy₀deg]
      exact Nat.cast_injective h1
    have hdvd : Nat.card h.D ∣ Work.CharCore.irrDeg χ := ⟨Work.CharCore.irrDeg θ, hdegχ⟩
    have hχ1 : χ 1 = ((Work.CharCore.irrDeg χ / Nat.card h.D : ℕ) : ℂ) * (y₀ 1) := by
      have h1 : ((Nat.card h.D * (Work.CharCore.irrDeg χ / Nat.card h.D) : ℕ) : ℂ)
          = (Work.CharCore.irrDeg χ : ℂ) := by
        rw [Nat.mul_div_cancel' hdvd]
      rw [Work.CharCore.irrDeg_spec hχIrr, hy₀deg, ← h1]
      push_cast
      ring
    have hineq' := hineq y₀ hy₀S0 (Work.CharCore.irrDeg χ / Nat.card h.D) hχ1
    rw [hy₀irrDeg] at hineq'
    omega

end Work.FeitSibley.Coherence
