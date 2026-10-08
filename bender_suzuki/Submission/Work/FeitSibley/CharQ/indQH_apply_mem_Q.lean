import Mathlib
import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.Induction.indFun_trans
import Submission.Work.Induction.indFun_TI_apply

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.indQH_apply_mem_Q`

For the Feit–Sibley configuration `h : FSData G`, `Ind_Q^H φ` and `Ind_Q^G φ` agree on
non-identity elements of `Q`.  Both are equal to `|Q|⁻¹ · ∑_{x ∈ N_G(Q)} φ (x q x⁻¹)`:
* for `Ind_Q^G` this is the T.I. restriction formula (`Work.Induction.indFun_TI_apply`), the
  normalizer being `N_G(Q) = H` (`h.normalizer_Q_eq`);
* for `Ind_Q^H` the sum is over `H` directly, and every conjugate `x q x⁻¹` (`x ∈ H`) lies in `Q`
  because `Q ◁ H`; the two sums then differ only in indexing.

The general statement behind this is `indFun_eq_indFun_subgroupOf`: if `K ≤ H ≤ G` with
`N_G(K) ≤ H` and `K` a T.I. subgroup, then for `1 ≠ g ∈ K` the induced function `Ind_K^G φ` and
the induced function `Ind_{K}^{H} φ` (computed inside `H`) agree at `g`.  Its proof reduces both
sides, via `Work.Induction.indFun_eq_sum_extZero` and `Work.Induction.indFun_subgroupOf_apply`,
to a sum of `extZero K φ (z * g * z⁻¹)` over `G` respectively over `H`; both sums have support
`N_G(K)` (T.I. condition, `extZero_conj_of_notMem_normalizer_eq_zero`), which is contained in
`H`, and hence agree.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical
open scoped Pointwise

namespace Work.FeitSibley.CharQ

variable {G : Type} [Group G]

/-! ### Sum bookkeeping for supported functions -/

/-- A sum over a group `G` of a function supported on a subgroup `S` is the sum over `S`. -/
theorem sum_eq_sum_subgroup_of_forall_notMem [Fintype G] (S : Subgroup G) (F : G → ℂ)
    (hzero : ∀ z : G, z ∉ S → F z = 0) :
    (∑ z : G, F z) = ∑ z : ↥S, F (z : G) := by
  have h1 : (∑ z : G, F z) = ∑ z : G, (if z ∈ S then F z else 0) := by
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases hz : z ∈ S
    · simp [hz]
    · simp [hz, hzero z hz]
  rw [h1, ← Work.Induction.sum_dite_mem_subgroup S (fun z : ↥S => F (z : G))]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases hz : z ∈ S <;> simp [hz]

/-- A sum over a subgroup `S` of a function supported on a subgroup `T ≤ S` is the sum over `T`. -/
theorem sum_subgroup_eq_sum_subgroup_of_le [Fintype G] (S T : Subgroup G) (hTS : T ≤ S)
    (F : G → ℂ) (hzero : ∀ z : G, z ∉ T → F z = 0) :
    (∑ x : ↥S, F (x : G)) = ∑ x : ↥T, F (x : G) := by
  have h1 : (∑ x : ↥S, F (x : G)) = ∑ x : ↥S, (if (x : G) ∈ T then F (x : G) else 0) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : (x : G) ∈ T
    · simp [hx]
    · simp [hx, hzero (x : G) hx]
  have h2 : (∑ x : ↥S, (if (x : G) ∈ T then F (x : G) else 0))
      = ∑ x : ↥(T.subgroupOf S), F ((x : ↥S) : G) := by
    rw [← Work.Induction.sum_dite_mem_subgroup (G := ↥S) (S := T.subgroupOf S)
      (fun x : ↥(T.subgroupOf S) => F ((x : ↥S) : G))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : (x : G) ∈ T
    · rw [ite_eq_left hx, dite_eq_left (Subgroup.mem_subgroupOf.mpr hx)]
    · rw [ite_eq_right hx, dite_eq_right (fun h => hx ((Subgroup.mem_subgroupOf).mp h))]
  have h3 : (∑ x : ↥(T.subgroupOf S), F ((x : ↥S) : G)) = ∑ x : ↥T, F (x : G) := by
    simpa using Equiv.sum_comp (Subgroup.subgroupOfEquivOfLe hTS).toEquiv (fun y : ↥T => F (y : G))
  rw [h1, h2, h3]

/-! ### The T.I. support condition -/

/-- If `K` is a T.I. subgroup and `1 ≠ g ∈ K`, then for `z ∉ N_G(K)` the term
`extZero K φ (z * g * z⁻¹)` vanishes: otherwise `g` would lie in `K ⊓ K^z = 1`. -/
theorem extZero_conj_of_notMem_normalizer_eq_zero {K : Subgroup G}
    (hTI : Work.Induction.IsTI K) {φ : ↥K → ℂ} {g : ↥K} (hg : g ≠ 1)
    {z : G} (hz : z ∉ Subgroup.normalizer (K : Set G)) :
    Work.Induction.extZero K φ (z * (g : G) * z⁻¹) = 0 := by
  rw [Work.Induction.extZero]
  by_cases hmem : z * (g : G) * z⁻¹ ∈ K
  · exfalso
    have hzinv : z⁻¹ ∉ Subgroup.normalizer (K : Set G) :=
      fun hc => hz (by simpa using (inv_mem hc))
    have hbot := hTI z⁻¹ hzinv
    have hmem' : (g : G) ∈ K ⊓ (MulAut.conj z⁻¹ • K) := by
      refine ⟨g.2, ?_⟩
      refine (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨z * (g : G) * z⁻¹, hmem, ?_⟩
      rw [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [hbot] at hmem'
    exact hg (Subtype.ext (by simpa using hmem'))
  · rw [dite_eq_right hmem]

/-! ### Induction inside a subgroup vs. inside the ambient group -/

/-- **Induction from `K` in `G` and in `H` agree on `K ∖ {1}`.**  Let `K ≤ H ≤ G` with
`N_G(K) ≤ H` and `K` T.I.; then for `1 ≠ g ∈ K` the function `Ind_K^G φ` computed in `G` and the
function `Ind_{K}^{H} φ` computed in `H` (with the pullback of `φ` along `K.subgroupOf H ≅ K`)
agree at `g`. -/
theorem indFun_eq_indFun_subgroupOf {G : Type} [Group G] [Fintype G] {K H : Subgroup G}
    (hKH : K ≤ H) (hN : Subgroup.normalizer (K : Set G) ≤ H) (hTI : Work.Induction.IsTI K)
    {φ : ↥K → ℂ} {g : ↥K} (hg : g ≠ 1) :
    Work.Induction.indFun K φ (g : G) =
      Work.Induction.indFun (K.subgroupOf H)
        (fun x : ↥(K.subgroupOf H) => φ ⟨(x : G), x.2⟩) ⟨(g : G), hKH g.2⟩ := by
  have hf : (fun x : ↥(K.subgroupOf H) => φ ⟨(x : G), x.2⟩)
      = fun x : ↥(K.subgroupOf H) => φ (Subgroup.subgroupOfEquivOfLe hKH x) := by
    funext x; exact congrArg φ (Subtype.ext rfl)
  have hcard : (Nat.card ↥(K.subgroupOf H) : ℂ) = (Nat.card ↥K : ℂ) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hsum : (∑ x : ↥H, Work.Induction.extZero K φ ((x : G) * (g : G) * (x : G)⁻¹))
      = ∑ z : G, Work.Induction.extZero K φ (z * (g : G) * z⁻¹) :=
    (sum_subgroup_eq_sum_subgroup_of_le H (Subgroup.normalizer (K : Set G)) hN
      (fun z : G => Work.Induction.extZero K φ (z * (g : G) * z⁻¹))
      (fun z hz => extZero_conj_of_notMem_normalizer_eq_zero hTI hg hz)).trans
    (sum_eq_sum_subgroup_of_forall_notMem (Subgroup.normalizer (K : Set G))
      (fun z : G => Work.Induction.extZero K φ (z * (g : G) * z⁻¹))
      (fun z hz => extZero_conj_of_notMem_normalizer_eq_zero hTI hg hz)).symm
  rw [hf, Work.Induction.indFun_subgroupOf_apply hKH φ ⟨(g : G), hKH g.2⟩,
      Work.Induction.indFun_eq_sum_extZero K φ (g : G), hcard, hsum]

/-! ### The lemma -/

theorem indQH_apply_mem_Q {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {φ : ↥h.Q → ℂ} (hφ : Work.CharCore.IsClassFun φ) {q : ↥h.Q} (hq : q ≠ 1) :
    h.indQH φ ⟨(q : G), h.Q_le_H q.2⟩ = Work.Induction.indFun h.Q φ (q : G) := by
  have hN : Subgroup.normalizer (h.Q : Set G) ≤ h.H := le_of_eq h.normalizer_Q_eq
  exact (indFun_eq_indFun_subgroupOf h.Q_le_H hN h.isTI_Q hq).symm

end Work.FeitSibley.CharQ
