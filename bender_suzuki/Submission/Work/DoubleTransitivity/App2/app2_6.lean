import Mathlib
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.DoubleTransitivity.App2.app2_3
import Submission.Work.DoubleTransitivity.App2.app2_5

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Appendix II (6)

`Work.DoubleTransitivity.App2.app2_6`: let `X` be a finite group acting `2`-transitively on a
finite set `E`, let `p` be a prime and let `P ≤ X_a` be a `p`-subgroup which is maximal among
the `p`-subgroups of the point stabiliser `X_a` fixing at least three points of `E`.  Then `P`
is maximal among *all* `p`-subgroups of `X` fixing at least three points, and the normaliser
`N_X(P)` acts `2`-transitively on the fixed point set `E_P`.

Proof (Peterfalvi, p. 205, transcribed in `REFS/peterfalvi_I_app1_4.md`).  Write `D` for a
two-point stabiliser.

* If `P` is a `p`-Sylow subgroup of `X_a ⊓ X_c` for some `c ∈ E_P \ {a}`, Appendix II (5)
  (`app2_5`) gives the `2`-transitivity of `N_X(P)` on `E_P` directly.
* Otherwise, for every `c ∈ E_P \ {a}` the subgroup `P` is not a `p`-Sylow of `X_a ⊓ X_c`, so
  it is strictly contained in a `p`-subgroup `R_c ≤ (X_a ⊓ X_c) ⊓ N_X(P)`; maximality of `P`
  forces `E_{R_c}` to have exactly the two points `a, c`.  Moreover `N_X(P)` does not fix `a`:
  for distinct `c, d ∈ E_P \ {a}`, either `P` is a `p`-Sylow of `X_c ⊓ X_d`, and conjugating a
  2-transitivity element and using Sylow conjugacy inside `X_c ⊓ X_d` produces an element of
  `N_X(P)` sending `a` to `c`, or it is not, and a `p`-subgroup of `X_c ⊓ X_d` strictly
  containing `P` cannot lie in `X_a` (it would fix `a, c, d` and contradict maximality of `P`).
  Appendix II (3) (`app2_3`), applied to `N_X(P)` acting on the invariant subset `E_P`,
  then gives `2`-transitivity.
* The maximality statement follows: a `p`-subgroup `Q ≥ P` fixing three points is conjugated
  by an element of `N_X(P)` into `X_a` and hence equals `P` by maximality of `P` in `X_a`.
-/

open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.DoubleTransitivity.App2

open Work.DoubleTransitivity
open Submission.Blueprint

/-- From `p ∣ [G : P]` we get a `p`-subgroup of `G` strictly containing `P`. -/
theorem a6_exists_pSubgroup_lt_of_dvd_relIndex {X : Type} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {G P : Subgroup X} (hP : IsPGroup p P) (hPG : P ≤ G)
    (hdiv : p ∣ P.relIndex G) :
    ∃ Q : Subgroup X, P < Q ∧ Q ≤ G ∧ IsPGroup p Q := by
  classical
  obtain ⟨S, hPS⟩ := (hP.comap_subtype (K := G)).exists_le_sylow
  have hne : (S : Subgroup ↥G) ≠ P.subgroupOf G := by
    intro heq
    have h2 := Sylow.not_dvd_index S
    rw [heq] at h2
    exact h2 hdiv
  have hle : P ≤ (S : Subgroup ↥G).map G.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPG]
    exact Subgroup.map_mono hPS
  refine ⟨(S : Subgroup ↥G).map G.subtype, ?_, Subgroup.map_subtype_le _,
    S.isPGroup'.map G.subtype⟩
  obtain ⟨-, x, hxS, hxP⟩ := SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne hPS hne.symm)
  refine lt_of_le_of_ne hle fun heq => hxP ?_
  rw [heq]
  exact Subgroup.mem_map_of_mem G.subtype hxS

/-- A `p`-subgroup `P` of `G` which is not a Sylow `p`-subgroup of `G` is strictly contained
in a `p`-subgroup of `N_G(P) ⊓ G`. -/
theorem a6_exists_pSubgroup_gt_in_normalizer {X : Type} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {G P : Subgroup X} (hP : IsPGroup p P) (hPG : P ≤ G)
    (hdiv : p ∣ P.relIndex G) :
    ∃ R : Subgroup X, IsPGroup p R ∧ P ≤ R ∧ R ≠ P ∧
      R ≤ Subgroup.normalizer (P : Set X) ∧ R ≤ G := by
  obtain ⟨Q, hPQ, hQG, hQg⟩ := a6_exists_pSubgroup_lt_of_dvd_relIndex hP hPG hdiv
  have hlt : P < Q ⊓ Subgroup.normalizer (P : Set X) := by
    refine lt_of_le_of_ne (le_inf hPQ.le Subgroup.le_normalizer) ?_
    intro heq
    have hle : Subgroup.normalizer (P : Set X) ⊓ Q ≤ P := by rw [inf_comm, ← heq]
    exact hPQ.ne' (app2_2_eq_of_normalizer_inf_eq (Q := P) (R := Q) hQg hPQ.le hle)
  exact ⟨Q ⊓ Subgroup.normalizer (P : Set X), hQg.to_inf_left, hlt.le, hlt.ne', inf_le_right,
    le_trans inf_le_left hQG⟩

/-- Peterfalvi, Appendix II (6): if `P` is not a Sylow `p`-subgroup of `X_a ⊓ X_c`, then `P` is
strictly contained in a `p`-subgroup of `N_X(P) ⊓ X_a` whose fixed point set is exactly
`{a, c}`. -/
theorem a6_fix_pair_of_not_sylow {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} [Fact p.Prime] {a c : E} {P : Subgroup X} (hP : IsPGroup p P)
    (ha : a ∈ (fixedBySub P : Set E)) (hc : c ∈ (fixedBySub P : Set E)) (hac : c ≠ a)
    (hnotsyl : ¬ IsSylowSubgroupOf p P
      (MulAction.stabilizer X a ⊓ MulAction.stabilizer X c))
    (hmax : ∀ Q : Subgroup X, IsPGroup p Q → Q ≤ MulAction.stabilizer X a →
      3 ≤ (fixedBySub Q : Set E).ncard → P ≤ Q → Q ≤ P) :
    ∃ R : Subgroup X, IsPGroup p R ∧ P ≤ R ∧
      R ≤ Subgroup.normalizer (P : Set X) ⊓ MulAction.stabilizer X a ∧
      fixedBySub R = {a, c} := by
  have hPa : P ≤ MulAction.stabilizer X a :=
    fun m hm => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp ha) m hm)
  have hPc : P ≤ MulAction.stabilizer X c :=
    fun m hm => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp hc) m hm)
  have hPD : P ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X c := le_inf hPa hPc
  have hdvd : p ∣ P.relIndex (MulAction.stabilizer X a ⊓ MulAction.stabilizer X c) := by
    by_contra hcon
    exact hnotsyl ⟨hPD, hP, hcon⟩
  obtain ⟨R, hRpg, hPR, hRne, hRN, hRD⟩ := a6_exists_pSubgroup_gt_in_normalizer hP hPD hdvd
  have hRa : R ≤ MulAction.stabilizer X a := le_trans hRD inf_le_left
  have hRc : R ≤ MulAction.stabilizer X c := le_trans hRD inf_le_right
  refine ⟨R, hRpg, hPR, le_inf hRN hRa, ?_⟩
  have hsub : ({a, c} : Set E) ⊆ (fixedBySub R : Set E) := by
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact fun m hm => MulAction.mem_stabilizer_iff.mp (hRa hm)
    · rw [hx]; exact fun m hm => MulAction.mem_stabilizer_iff.mp (hRc hm)
  have hle2 : (fixedBySub R : Set E).ncard ≤ ({a, c} : Set E).ncard := by
    rw [Set.ncard_pair hac.symm]
    by_contra hcon
    exact hRne (le_antisymm (hmax R hRpg hRa (by omega) hPR) hPR)
  exact (Set.eq_of_subset_of_ncard_le hsub hle2).symm

/-- Peterfalvi, Appendix II (6): `N_X(P)` does not fix `a`. -/
theorem a6_normalizer_not_fix {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} [Fact p.Prime] {a : E} {P : Subgroup X} (hP : IsPGroup p P)
    (hPa : P ≤ MulAction.stabilizer X a) (hbig : 3 ≤ (fixedBySub P : Set E).ncard)
    (h2 : MulAction.IsMultiplyPretransitive X E 2)
    (hmax : ∀ Q : Subgroup X, IsPGroup p Q → Q ≤ MulAction.stabilizer X a →
      3 ≤ (fixedBySub Q : Set E).ncard → P ≤ Q → Q ≤ P) :
    ∃ k ∈ Subgroup.normalizer (P : Set X), k • a ≠ a := by
  classical
  have haP : a ∈ (fixedBySub P : Set E) :=
    fun m hm => MulAction.mem_stabilizer_iff.mp (hPa hm)
  have hle_of_mem : ∀ x : E, x ∈ (fixedBySub P : Set E) → P ≤ MulAction.stabilizer X x :=
    fun x hx m hm => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp hx) m hm)
  -- two distinct points `c`, `d` of `E_P \ {a}`
  have hT : 2 ≤ ((fixedBySub P : Set E) \ {a}).ncard := by
    have hsub : (fixedBySub P : Set E) ⊆ insert a ((fixedBySub P : Set E) \ {a}) := by
      intro x hx
      by_cases hxa : x = a
      · exact Set.mem_insert_iff.mpr (Or.inl hxa)
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨hx, hxa⟩)
    have h1 := Set.ncard_le_ncard hsub
    have h2' := Set.ncard_insert_le a ((fixedBySub P : Set E) \ {a})
    omega
  have hnonempty : ((fixedBySub P : Set E) \ {a}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    omega
  obtain ⟨c, hcT⟩ := hnonempty
  obtain ⟨d, hdT, hdc⟩ :=
    Set.exists_ne_of_one_lt_ncard (show 1 < ((fixedBySub P : Set E) \ {a}).ncard by omega) c
  have hcP : c ∈ (fixedBySub P : Set E) := hcT.1
  have hca : c ≠ a := hcT.2
  have hdP : d ∈ (fixedBySub P : Set E) := hdT.1
  have hda : d ≠ a := hdT.2
  have hPcd : P ≤ MulAction.stabilizer X c ⊓ MulAction.stabilizer X d :=
    le_inf (hle_of_mem c hcP) (hle_of_mem d hdP)
  by_cases hsyl : IsSylowSubgroupOf p P
      (MulAction.stabilizer X c ⊓ MulAction.stabilizer X d)
  · -- Case 1: `P` is a Sylow `p`-subgroup of `X_c ⊓ X_d`
    obtain ⟨g, hga, hgc⟩ :=
      (MulAction.is_two_pretransitive_iff.mp h2) hca.symm hdc.symm
    have hconjD : MulAction.stabilizer X c ⊓ MulAction.stabilizer X d
        = conj g (MulAction.stabilizer X a ⊓ MulAction.stabilizer X c) :=
      stabilizer_inf_conj hga hgc
    have hconjP : conj g P ≤ MulAction.stabilizer X c ⊓ MulAction.stabilizer X d := by
      rw [hconjD]
      exact Subgroup.map_mono (le_inf (hle_of_mem a haP) (hle_of_mem c hcP))
    have hSyl : IsSylowSubgroupOf p (conj g P)
        (MulAction.stabilizer X c ⊓ MulAction.stabilizer X d) := by
      refine isSylowSubgroupOf_of_le_conj (t := g⁻¹) ?_ hconjP (hP.map _)
      rw [conj_inv_conj]
      exact hsyl
    obtain ⟨y, hy, hyconj⟩ := sylow_conj_in_subgroup hSyl hsyl
    refine ⟨y * g, ?_, ?_⟩
    · rw [← conj_eq_self_iff_mem_normalizer]
      rw [conj_mul, hyconj]
    · show (y * g) • a ≠ a
      have hyc : y • c = c := MulAction.mem_stabilizer_iff.mp hy.1
      rw [mul_smul, hga, hyc]
      exact hca
  · -- Case 2: `P` is not a Sylow `p`-subgroup of `X_c ⊓ X_d`
    have hdvd : p ∣ P.relIndex (MulAction.stabilizer X c ⊓ MulAction.stabilizer X d) := by
      by_contra hcon
      exact hsyl ⟨hPcd, hP, hcon⟩
    obtain ⟨R, hRpg, hPR, hRne, hRN, hRcd⟩ :=
      a6_exists_pSubgroup_gt_in_normalizer hP hPcd hdvd
    by_cases hRa : R ≤ MulAction.stabilizer X a
    · exfalso
      have hsub : ({a, c, d} : Set E) ⊆ (fixedBySub R : Set E) := by
        intro x hx
        rcases hx with hx | hx | hx
        · rw [hx]; exact fun m hm => MulAction.mem_stabilizer_iff.mp (hRa hm)
        · rw [hx]
          exact fun m hm => MulAction.mem_stabilizer_iff.mp ((le_trans hRcd inf_le_left) hm)
        · rw [hx]
          exact fun m hm => MulAction.mem_stabilizer_iff.mp ((le_trans hRcd inf_le_right) hm)
      have h3 : 3 ≤ (fixedBySub R : Set E).ncard := by
        have h1 := Set.ncard_le_ncard hsub
        have hcard : ({a, c, d} : Set E).ncard = 3 := by
          rw [Set.ncard_eq_three]
          exact ⟨a, c, d, hca.symm, hda.symm, hdc.symm, rfl⟩
        omega
      exact hRne (le_antisymm (hmax R hRpg hRa h3 hPR) hPR)
    · have hnot : ¬ ∀ r ∈ R, r • a = a :=
        fun hcon => hRa fun r hr => MulAction.mem_stabilizer_iff.mpr (hcon r hr)
      obtain ⟨r, hri⟩ := not_forall.mp hnot
      have hrR : r ∈ R := by
        by_contra hr
        exact hri fun hr' => absurd hr' hr
      have hra : r • a ≠ a := fun hcon => hri fun _ => hcon
      exact ⟨r, hRN hrR, hra⟩

/-- Peterfalvi, Appendix II (3) applied to `K` acting on the invariant subset `S`. -/
theorem a6_twoTransitive_of_fix_pair {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} [Fact p.Prime] {K : Subgroup X} {S : Set E} {a : E}
    (hS : ∀ k ∈ K, ∀ s ∈ S, k • s ∈ S) (ha : a ∈ S)
    (h : ∀ c ∈ S, c ≠ a → ∃ R : Subgroup X, IsPGroup p R ∧ R ≤ K ∧
      R ≤ MulAction.stabilizer X a ∧ fixedBySub R ∩ S = {a, c})
    (hmoved : ∃ k ∈ K, k • a ≠ a) :
    IsTwoTransitiveOnSub K S := by
  classical
  let S' : SubMulAction K E := { carrier := S, smul_mem' := fun k x hx => hS k.1 k.2 x hx }
  haveI : Fintype ↥S := (Set.toFinite S).fintype
  haveI : Fintype S' := ‹Fintype ↥S›
  have hmain : MulAction.IsMultiplyPretransitive K S' 2 := by
    refine app2_3 (X := K) (E := S') (p := p) (a := ⟨a, ha⟩) ?_ ?_
    · intro c hc
      rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
      obtain ⟨R, hRpg, hRK, hRa, hRfix⟩ := h c.1 c.2 (fun hca => hc (Subtype.ext hca))
      have haR : a ∈ fixedBySub R := by
        have h : a ∈ fixedBySub R ∩ S := by rw [hRfix]; exact Or.inl rfl
        exact h.1
      have hcR : c.1 ∈ fixedBySub R := by
        have h : c.1 ∈ fixedBySub R ∩ S := by rw [hRfix]; exact Or.inr rfl
        exact h.1
      refine ⟨R.subgroupOf K, hRpg.comap_subtype, ?_⟩
      ext z
      rw [mem_fixedBySub]
      constructor
      · intro hz
        have hzR : (z : E) ∈ fixedBySub R := by
          intro r hr
          have hmem : (⟨r, hRK hr⟩ : K) ∈ R.subgroupOf K := Subgroup.mem_subgroupOf.mpr hr
          have h2 := hz ⟨r, hRK hr⟩ hmem
          have h3 := congrArg (fun y : S' => (y : E)) h2
          simpa [SubMulAction.val_smul, Subgroup.mk_smul] using h3
        have hzRS : (z : E) ∈ fixedBySub R ∩ S := ⟨hzR, z.2⟩
        rw [hRfix] at hzRS
        rcases hzRS with h' | h'
        · exact Or.inl (Subtype.ext h')
        · exact Or.inr (Subtype.ext h')
      · intro hz
        rcases hz with h' | h'
        · subst h'
          intro m hm
          apply Subtype.ext
          simpa [SubMulAction.val_smul, Subgroup.smul_def] using
            (mem_fixedBySub.mp haR) (m : X) (Subgroup.mem_subgroupOf.mp hm)
        · subst h'
          intro m hm
          apply Subtype.ext
          simpa [SubMulAction.val_smul, Subgroup.smul_def] using
            (mem_fixedBySub.mp hcR) (m : X) (Subgroup.mem_subgroupOf.mp hm)
    · intro hcon
      obtain ⟨k, hkK, hka⟩ := hmoved
      exact hka (congrArg (fun y : S' => (y : E)) (hcon ⟨k, hkK⟩))
  intro c hc d hd hcd c' hc' d' hd' hcd'
  obtain ⟨g, hg1, hg2⟩ := (MulAction.is_two_pretransitive_iff.mp hmain)
    (show (⟨c, hc⟩ : S') ≠ ⟨d, hd⟩ from fun hh => hcd (Subtype.ext_iff.mp hh))
    (show (⟨c', hc'⟩ : S') ≠ ⟨d', hd'⟩ from fun hh => hcd' (Subtype.ext_iff.mp hh))
  exact ⟨(g : X), g.2, congrArg (fun y : S' => (y : E)) hg1,
    congrArg (fun y : S' => (y : E)) hg2⟩

/-- Peterfalvi, Appendix II (6), maximality part. -/
theorem a6_maximal_of_transitive {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} [Fact p.Prime] {a : E} {P : Subgroup X} (hP : IsPGroup p P)
    (hPa : P ≤ MulAction.stabilizer X a)
    (hmax : ∀ Q : Subgroup X, IsPGroup p Q → Q ≤ MulAction.stabilizer X a →
      3 ≤ (fixedBySub Q : Set E).ncard → P ≤ Q → Q ≤ P)
    (htrans : ∀ c ∈ (fixedBySub P : Set E), ∃ y ∈ Subgroup.normalizer (P : Set X), y • a = c) :
    ∀ Q : Subgroup X, IsPGroup p Q → 3 ≤ (fixedBySub Q : Set E).ncard → P ≤ Q → Q ≤ P := by
  intro Q hQg hQbig hPQ
  obtain ⟨c, hcQ, hcne⟩ := Set.exists_ne_of_one_lt_ncard (show 1 < (fixedBySub Q : Set E).ncard by omega) a
  have hcP : c ∈ (fixedBySub P : Set E) := fixedBySub_antitone hPQ hcQ
  obtain ⟨y, hyN, hya⟩ := htrans c hcP
  have hyP : conj y P = P := (conj_eq_self_iff_mem_normalizer y P).mpr hyN
  have hyPinv : conj y⁻¹ P = P := by
    have h := conj_inv_conj y P
    rwa [hyP] at h
  have hQ'y : conj y⁻¹ Q ≤ MulAction.stabilizer X a := by
    intro z hz
    rw [mem_conj] at hz
    rw [MulAction.mem_stabilizer_iff]
    have hcy : y⁻¹ • c = a := by rw [← hya, inv_smul_smul]
    have hz' : y * z * y⁻¹ ∈ Q := by simpa only [inv_inv] using hz
    have hzc : (y * z * y⁻¹) • c = c := (mem_fixedBySub.mp hcQ) _ hz'
    calc z • a = (y⁻¹ * (y * z * y⁻¹) * y) • a := by
          rw [show y⁻¹ * (y * z * y⁻¹) * y = z from by group]
      _ = y⁻¹ • ((y * z * y⁻¹) • (y • a)) := by rw [mul_smul, mul_smul]
      _ = y⁻¹ • ((y * z * y⁻¹) • c) := by rw [hya]
      _ = y⁻¹ • c := by rw [hzc]
      _ = a := hcy
  have hQ'pg : IsPGroup p (conj y⁻¹ Q) := hQg.map _
  have hcard : 3 ≤ (fixedBySub (conj y⁻¹ Q) : Set E).ncard := by
    have h : (fixedBySub (conj y⁻¹ Q) : Set E) = y⁻¹ • (fixedBySub Q : Set E) :=
      app2_3_fixedBySub_map_conj Q y⁻¹
    rw [h, Set.ncard_smul_set]
    exact hQbig
  have hPQ' : P ≤ conj y⁻¹ Q := by
    rw [← hyPinv]
    exact Subgroup.map_mono hPQ
  have hle : conj y⁻¹ Q ≤ P := hmax (conj y⁻¹ Q) hQ'pg hQ'y hcard hPQ'
  have h2 : conj y (conj y⁻¹ Q) ≤ conj y P := Subgroup.map_mono hle
  rwa [conj_conj_inv, hyP] at h2

/-- Peterfalvi I, Appendix II (6). -/
theorem app2_6 {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} [Fact p.Prime] {a b : E} (hab : a ≠ b)
    (h2 : MulAction.IsMultiplyPretransitive X E 2)
    {P : Subgroup X} (hP : IsPGroup p P) (hPa : P ≤ MulAction.stabilizer X a)
    (hbig : 3 ≤ (fixedBySub P : Set E).ncard)
    (hmax : ∀ Q : Subgroup X, IsPGroup p Q → Q ≤ MulAction.stabilizer X a →
      3 ≤ (fixedBySub Q : Set E).ncard → P ≤ Q → Q ≤ P) :
    (∀ Q : Subgroup X, IsPGroup p Q → 3 ≤ (fixedBySub Q : Set E).ncard → P ≤ Q → Q ≤ P) ∧
    IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set X)) (fixedBySub P : Set E) := by
  classical
  set N : Subgroup X := Subgroup.normalizer (P : Set X) with hN
  set S : Set E := (fixedBySub P : Set E) with hS
  have haS : a ∈ S := by
    rw [hS]
    exact fun m hm => MulAction.mem_stabilizer_iff.mp (hPa hm)
  have haP : a ∈ (fixedBySub P : Set E) := by rwa [← hS]
  have hclosure : ∀ k ∈ N, ∀ s ∈ S, k • s ∈ S := by
    intro k hk s hs
    rw [hS] at hs ⊢
    exact smul_mem_fixedBySub_of_mem_normalizer (by rwa [hN] at hk) hs
  have hmain : IsTwoTransitiveOnSub N S := by
    by_cases hcase : ∀ c ∈ S, c ≠ a →
        ¬ IsSylowSubgroupOf p P (MulAction.stabilizer X a ⊓ MulAction.stabilizer X c)
    · have hfix : ∀ c ∈ S, c ≠ a → ∃ R : Subgroup X, IsPGroup p R ∧ R ≤ N ∧
          R ≤ MulAction.stabilizer X a ∧ fixedBySub R ∩ S = {a, c} := by
        intro c hc hcne
        have hc' : c ∈ (fixedBySub P : Set E) := by rwa [hS] at hc
        obtain ⟨R, hRpg, hPR, hRN, hRfix⟩ :=
          a6_fix_pair_of_not_sylow hP haP hc' hcne (hcase c hc hcne) hmax
        refine ⟨R, hRpg, by rw [hN]; exact le_trans hRN inf_le_left, le_trans hRN inf_le_right, ?_⟩
        rw [hRfix]
        exact Set.inter_eq_left.mpr (by
          intro x hx
          rcases hx with rfl | rfl
          · exact haS
          · exact hc)
      obtain ⟨k, hk, hka⟩ := a6_normalizer_not_fix hP hPa hbig h2 hmax
      exact a6_twoTransitive_of_fix_pair hclosure haS hfix ⟨k, by rw [hN]; exact hk, hka⟩
    · push Not at hcase
      obtain ⟨c, hc, hcne, hcsyl⟩ := hcase
      exact app2_5 hcne.symm h2 hcsyl
  have htrans : ∀ c ∈ S, ∃ y ∈ N, y • a = c := fun c hc => hmain.isTransitiveOnSub a haS c hc
  refine ⟨a6_maximal_of_transitive hP hPa hmax ?_, ?_⟩
  · simpa only [← hS, ← hN] using htrans
  · simpa only [← hN, ← hS] using hmain

end Work.DoubleTransitivity.App2
