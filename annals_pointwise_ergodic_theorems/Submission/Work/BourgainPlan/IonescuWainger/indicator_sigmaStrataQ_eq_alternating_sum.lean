import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.sigmaStrataQ_sum_ne_zero

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The strata indicator as an alternating sum of torsion-subgroup indicators

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4.

For a finite set `S` of pairwise coprime integers `≥ 2`, `Q_A = ∏_{q ∈ A} q`, and `A₀ ⊆ S`, the
stratum `Σ_{A₀}` of `sigmaStrataQ (QA S) A₀` is, by construction, the torsion subgroup
`Σ_{⊆ A₀} = 𝕋[Q_{A₀}]` minus all strictly smaller torsion subgroups `𝕋[Q_B]`, `B ⊊ A₀`.  The
Möbius/inclusion–exclusion inversion of that relation is the identity

`1_{Σ_{A₀}} = ∑_{B ⊆ A₀} (-1)^{|A₀| - |B|} 1_{Σ_{⊆ B}}`,

which is the statement proved here for the lifts to `ZMod (Q_S)`.

The mathematical content is entirely arithmetic.  Writing `m = addOrderOf x` for `x ∈ ZMod (Q_S)`,
the annihilator description `mem_sigmaSubAQ_iff` turns membership `x ∈ Σ_{⊆ B}` into the
divisibility `m ∣ Q_B`.  The family `B ↦ [m ∣ Q_B]` is then a *principal up-set* in the Boolean
lattice of subsets of `S`: the smallest `B` with `m ∣ Q_B` is

`T(x) = {q ∈ S : m ∤ Q_{S∖{q}}}`,

and the Boolean Möbius inversion of a principal up-set is the indicator of its generator.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BourgainPlan.IonescuWainger

/-! ## A combinatorial identity on the Boolean lattice -/

/-- `T ⊆ insert a B` is equivalent to `T.erase a ⊆ B` (no hypothesis on `a` and `B`). -/
lemma ite_subset_insert_erase (a : ℕ) (T B : Finset ℕ) :
    (if T ⊆ insert a B then (1 : ℂ) else 0) = (if T.erase a ⊆ B then (1 : ℂ) else 0) := by
  by_cases h : T ⊆ insert a B
  · rw [if_pos h, if_pos]
    intro x hx
    obtain ⟨hxa, hxT⟩ := Finset.mem_erase.mp hx
    rcases Finset.mem_insert.mp (h hxT) with h' | h'
    · exact absurd h' hxa
    · exact h'
  · rw [if_neg h, if_neg]
    intro hcontra
    apply h
    intro x hxT
    rw [Finset.mem_insert]
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (hcontra (Finset.mem_erase.mpr ⟨hxa, hxT⟩))

/-- **Boolean Möbius inversion of a principal up-set.**  For finsets `s, T`,
`∑_{B ⊆ s} (-1)^{|s|-|B|} 1_{T ⊆ B} = 1_{T = s}`. -/
lemma sum_powerset_ite_subset (s T : Finset ℕ) :
    ∑ B ∈ s.powerset, (-1 : ℂ) ^ (s.card - B.card) * (if T ⊆ B then (1 : ℂ) else 0)
      = if T = s then (1 : ℂ) else 0 := by
  classical
  induction s using Finset.induction_on generalizing T with
  | empty =>
      rw [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, tsub_zero, pow_zero,
        one_mul]
      by_cases h : T = ∅
      · rw [if_pos (Finset.subset_empty.mpr h), if_pos h]
      · rw [if_neg (fun hc => h (Finset.subset_empty.mp hc)), if_neg h]
  | insert a s' ha ih =>
      rw [Finset.powerset_insert]
      have hdisj : Disjoint s'.powerset (Finset.image (insert a) s'.powerset) := by
        rw [Finset.disjoint_left]
        intro B hB hB'
        rw [Finset.mem_powerset] at hB
        obtain ⟨C, hC, hCB⟩ := Finset.mem_image.mp hB'
        have : a ∈ B := hCB ▸ Finset.mem_insert_self a C
        exact ha (hB this)
      have hinj : Set.InjOn (insert a) ((s'.powerset : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
        intro B hB C hC hBC
        rw [Finset.mem_coe, Finset.mem_powerset] at hB hC
        rw [← Finset.erase_insert (fun h => ha (hB h)), hBC,
          Finset.erase_insert (fun h => ha (hC h))]
      have hterm1 : ∀ B ∈ s'.powerset,
          (-1 : ℂ) ^ ((insert a s').card - B.card) * (if T ⊆ B then (1 : ℂ) else 0)
            = (-1) * ((-1 : ℂ) ^ (s'.card - B.card) * (if T ⊆ B then (1 : ℂ) else 0)) := by
        intro B hB
        have hBle : B.card ≤ s'.card := Finset.card_le_card (Finset.mem_powerset.mp hB)
        rw [Finset.card_insert_of_notMem ha,
          show s'.card + 1 - B.card = (s'.card - B.card) + 1 by omega, pow_succ]
        ring
      have hsum1 : (∑ B ∈ s'.powerset,
            (-1 : ℂ) ^ ((insert a s').card - B.card) * (if T ⊆ B then (1 : ℂ) else 0))
          = -(if T = s' then (1 : ℂ) else 0) := by
        rw [Finset.sum_congr rfl hterm1, ← Finset.mul_sum, ih T, neg_one_mul]
      have hterm2 : ∀ B ∈ s'.powerset,
          (-1 : ℂ) ^ ((insert a s').card - (insert a B).card) *
              (if T ⊆ insert a B then (1 : ℂ) else 0)
            = (-1 : ℂ) ^ (s'.card - B.card) * (if T.erase a ⊆ B then (1 : ℂ) else 0) := by
        intro B hB
        have hBsub : B ⊆ s' := Finset.mem_powerset.mp hB
        have haB : a ∉ B := fun h => ha (hBsub h)
        rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haB,
          show s'.card + 1 - (B.card + 1) = s'.card - B.card by omega,
          ite_subset_insert_erase a T B]
      have hsum2 : (∑ B ∈ Finset.image (insert a) s'.powerset,
            (-1 : ℂ) ^ ((insert a s').card - B.card) * (if T ⊆ B then (1 : ℂ) else 0))
          = (if T.erase a = s' then (1 : ℂ) else 0) := by
        rw [Finset.sum_image hinj, Finset.sum_congr rfl hterm2, ih (T.erase a)]
      rw [Finset.sum_union hdisj, hsum1, hsum2]
      by_cases haT : a ∈ T
      · have hne : T ≠ s' := fun h => ha (h ▸ haT)
        have hif : (if T.erase a = s' then (1 : ℂ) else 0) =
            (if T = insert a s' then (1 : ℂ) else 0) := by
          by_cases h : T = insert a s'
          · rw [if_pos h, if_pos (by rw [h, Finset.erase_insert ha])]
          · rw [if_neg h, if_neg]
            intro h'
            exact h (by rw [← Finset.insert_erase haT, h'])
        rw [if_neg hne, neg_zero, zero_add]
        exact hif
      · have herase : T.erase a = T := Finset.erase_eq_of_notMem haT
        rw [herase, neg_add_cancel]
        exact (if_neg (fun h : T = insert a s' =>
          haT (h.symm ▸ Finset.mem_insert_self a s'))).symm

/-! ## The arithmetic of the torsion subgroups -/

/-- **Key divisibility lemma.**  Let `S` be a finset of pairwise coprime integers, `m ∣ Q_S`.  If
`m` divides `Q_{S∖{q}}` for every `q ∈ C` (`C ⊆ S`), then `m` divides `Q_{S∖C}`.

Proof by induction on `C`: for a newly added `a`, `Q_{S∖C'}` and `Q_{S∖{a}}` have gcd
`Q_{(S∖C')∖{a}}` (`gcd_QA_inter_of_coprime`), so `m` divides that gcd. -/
lemma dvd_QA_sdiff_of_forall {S : Finset ℕ} {m : ℕ}
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (hm : m ∣ QA S) :
    ∀ (C : Finset ℕ), C ⊆ S → (∀ q ∈ C, m ∣ QA (S.erase q)) → m ∣ QA (S \ C) := by
  intro C
  induction C using Finset.induction_on with
  | empty => intro _ _; simpa using hm
  | insert a C' ha ih =>
      intro hC h
      have haS : a ∈ S := hC (Finset.mem_insert_self a C')
      have hC' : C' ⊆ S := fun x hx => hC (Finset.mem_insert_of_mem hx)
      have ih' : m ∣ QA (S \ C') := ih hC' (fun q hq => h q (Finset.mem_insert_of_mem hq))
      have ha' : m ∣ QA (S.erase a) := h a (Finset.mem_insert_self a C')
      have hgcd : Nat.gcd (QA (S \ C')) (QA (S.erase a)) = QA ((S \ C') \ {a}) := by
        rw [gcd_QA_inter_of_coprime (A := S \ C') (B := S.erase a)
          (fun p hp q hq hpq =>
            hcop p (Finset.mem_sdiff.mp hp).1 q (Finset.mem_erase.mp hq).2 hpq)]
        congr 1
        ext x
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
        tauto
      have hgoal : m ∣ QA ((S \ C') \ {a}) := by
        rw [← hgcd]; exact Nat.dvd_gcd ih' ha'
      rwa [Finset.sdiff_insert, Finset.erase_eq]

/-- **The principal up-set description of `m ∣ Q_B`.**  If `m ∣ Q_S`, then for `B ⊆ S`,
`m ∣ Q_B` if and only if `B` contains `T = {q ∈ S : m ∤ Q_{S∖{q}}}`. -/
lemma dvd_QA_iff_filter_subset {S B : Finset ℕ} {m : ℕ}
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (hm : m ∣ QA S) (hB : B ⊆ S) :
    m ∣ QA B ↔ S.filter (fun q => ¬ (m ∣ QA (S.erase q))) ⊆ B := by
  classical
  constructor
  · intro hBdvd q hq
    obtain ⟨hqS, hqndvd⟩ := Finset.mem_filter.mp hq
    by_contra hqB
    have hsub : B ⊆ S.erase q := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun h => hqB (h ▸ hx), hB hx⟩
    exact hqndvd (dvd_trans hBdvd
      (Finset.prod_dvd_prod_of_subset B (S.erase q) (fun i => i) hsub))
  · intro hTB
    have h : ∀ q ∈ S \ B, m ∣ QA (S.erase q) := by
      intro q hq
      obtain ⟨hqS, hqB⟩ := Finset.mem_sdiff.mp hq
      by_contra hnd
      exact hqB (hTB (Finset.mem_filter.mpr ⟨hqS, hnd⟩))
    have hmain := dvd_QA_sdiff_of_forall hcop hm (S \ B) (Finset.sdiff_subset) h
    have hset : S \ (S \ B) = B := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxS, hx⟩ := Finset.mem_sdiff.mp hx
        by_contra h
        exact hx (Finset.mem_sdiff.mpr ⟨hxS, h⟩)
      · intro hx
        exact Finset.mem_sdiff.mpr ⟨hB hx, fun h => (Finset.mem_sdiff.mp h).2 hx⟩
    rwa [hset] at hmain

/-- A finset equals `A₀` iff it is contained in `A₀` and in no proper subset of `A₀`. -/
lemma eq_iff_subset_and_proper_not_subset {T A₀ : Finset ℕ} :
    T = A₀ ↔ T ⊆ A₀ ∧ ∀ B ∈ A₀.powerset.erase A₀, ¬ T ⊆ B := by
  constructor
  · rintro rfl
    refine ⟨Finset.Subset.refl _, ?_⟩
    intro B hB hTB
    rw [Finset.mem_erase, Finset.mem_powerset] at hB
    exact hB.1 (Finset.Subset.antisymm hB.2 hTB)
  · rintro ⟨hsub, hnot⟩
    by_contra hne
    exact hnot T (Finset.mem_erase.mpr ⟨hne, Finset.mem_powerset.mpr hsub⟩) (Finset.Subset.refl T)

/-! ## The main identity -/

theorem indicator_sigmaStrataQ_eq_alternating_sum {S : Finset ℕ} [NeZero (QA S)]
    (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S) (x : ZMod (QA S)) :
    ∑ B ∈ A₀.powerset, (-1 : ℂ) ^ (A₀.card - B.card) *
        (if x ∈ sigmaSubAQ (QA S) B then (1 : ℂ) else 0)
      = if x ∈ sigmaStrataQ (QA S) A₀ then (1 : ℂ) else 0 := by
  classical
  have hmS : addOrderOf x ∣ QA S := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  set T : Finset ℕ := S.filter (fun q => ¬ (addOrderOf x ∣ QA (S.erase q))) with hT_def
  have hmem : ∀ B ∈ A₀.powerset, (x ∈ sigmaSubAQ (QA S) B) ↔ T ⊆ B := by
    intro B hB
    have hBsub : B ⊆ S := (Finset.mem_powerset.mp hB).trans hA₀
    rw [mem_sigmaSubAQ_iff (Q := QA S) (A := B)
        (Finset.prod_dvd_prod_of_subset B S (fun i => i) hBsub) x,
      ← addOrderOf_dvd_iff_nsmul_eq_zero]
    exact dvd_QA_iff_filter_subset hS hmS hBsub
  have hLHS : (∑ B ∈ A₀.powerset, (-1 : ℂ) ^ (A₀.card - B.card) *
        (if x ∈ sigmaSubAQ (QA S) B then (1 : ℂ) else 0))
      = ∑ B ∈ A₀.powerset, (-1 : ℂ) ^ (A₀.card - B.card) * (if T ⊆ B then (1 : ℂ) else 0) := by
    refine Finset.sum_congr rfl (fun B hB => ?_)
    by_cases hx : x ∈ sigmaSubAQ (QA S) B
    · rw [if_pos hx, if_pos ((hmem B hB).mp hx)]
    · rw [if_neg hx, if_neg (fun hT => hx ((hmem B hB).mpr hT))]
  have hRHS : (x ∈ sigmaStrataQ (QA S) A₀) ↔ T = A₀ := by
    have hA₀dvd : QA A₀ ∣ QA S := Finset.prod_dvd_prod_of_subset A₀ S (fun i => i) hA₀
    have hmemA : (x ∈ sigmaSubAQ (QA S) A₀) ↔ T ⊆ A₀ := by
      rw [mem_sigmaSubAQ_iff (Q := QA S) (A := A₀) hA₀dvd x,
        ← addOrderOf_dvd_iff_nsmul_eq_zero]
      exact dvd_QA_iff_filter_subset hS hmS hA₀
    have hmemB : ∀ B ∈ A₀.powerset.erase A₀, (x ∈ sigmaSubAQ (QA S) B) ↔ T ⊆ B :=
      fun B hB => hmem B (Finset.mem_of_mem_erase hB)
    rw [sigmaStrataQ, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2'⟩
      rw [hmemA] at h1
      exact eq_iff_subset_and_proper_not_subset.mpr
        ⟨h1, fun B hB hTB => h2' B hB ((hmemB B hB).mpr hTB)⟩
    · intro hT
      obtain ⟨h1, h2'⟩ := eq_iff_subset_and_proper_not_subset.mp hT
      exact ⟨hmemA.mpr h1,
        fun B hB => (not_congr (hmemB B hB)).mpr (h2' B hB)⟩
  rw [hLHS, sum_powerset_ite_subset]
  by_cases h : T = A₀
  · rw [if_pos h, if_pos (hRHS.mpr h)]
  · rw [if_neg h, if_neg (fun hx => h (hRHS.mp hx))]

end Work.BourgainPlan.IonescuWainger
