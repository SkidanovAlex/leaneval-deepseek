/-
# Peterfalvi I Ch. III §2 Prop. 1, without the `KInvariantUnderD` input

The lead's ruling (`NOTES_LEAD_bs_appxgap.md`) that `KInvariantUnderD H t` is not needed, carried
out.  The point of the present proof is that **no conjugation of `K = J(D,t)` is ever performed**:
the case split of the paper is made on subgroups of `E = W ⊓ D` that already lie in
`V = centD H t`.

* If the `p`-Sylow `P₀` of `E` has exactly two fixed points, it is used as it stands (case 1 for
  `P₀`, and for every non-cyclic `U ≤ P₀` which has exactly two fixed points).  A non-cyclic
  `U ≤ P₀` with at least three fixed points is `D`-conjugated into `V`; at its conjugate the
  case-2 normaliser condition is *derived from scratch*: if `U^d` acted fixed-point-freely on `K`
  then `U^d` would be cyclic (App. I (5)(c), `cyclic_of_fpf_on_centD`, applicable since
  `U^d ≤ V`), contradicting non-cyclicity.  Hence `U^d` is not fixed-point-free on `K`, i.e. there
  are `1 ≠ x ∈ U^d` and `1 ≠ k ∈ K` with `x k x⁻¹ = k`; taking `U₁ = ⟨x⟩` (subnormal in the
  `p`-group `U^d`) and `Y = U₁` gives the hypothesis of Ch. II §4 Prop. 3(b) at `U^d` **without
  transporting `k`** — `k` is already the required witness for `U^d`.  The normaliser identity is
  then carried back to `U` by `normalizerCond_conj`.

* If `P₀` has at least three fixed points, we conjugate it into `V` **once and for all** and use
  `P := P₀^d ≤ V` as the Sylow in the `p`-control criterion `pcontrol_prod_v2`.  Then every `U ≤ P`
  lies in `V`, so the argument above applies to `P` and to every non-cyclic `U ≤ P` directly, with
  no transport at all: either `P` is fixed-point-free on `K` (and then cyclic, giving the second
  alternative of `Section2Prop'`), or `P` is not, and the criterion's two hypotheses are verified.

Everything else (case 1, the failure-of-fixed-point-freeness witness, the `p`-control criterion) is
as in `section2_prop1_v2`.
-/
import Mathlib
import Submission.Work.NormalComplement.SectionsV3
import Submission.Work.NormalComplement.section2_prop1_v2
import Submission.Work.NormalComplement.case2_normalizer_le_v3
import Submission.Work.NormalComplement.case2_prop3b_v3
import Submission.Work.NormalComplement.normalizerCond_conj
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.case1_normalizer_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **Peterfalvi I Ch. III §2 Proposition 1** (p.175), in the `KInvariantUnderD`-free form
`Work.NormalComplement.Section2Prop'`: with `H` strongly embedded, `t ∉ H` an involution,
`D = H ∩ H^t`, `W ⊴ H` with `H = W·D`, `E = W ∩ D` and `p ∣ |E|`: either `E` is `p`-control in
`W`, or `E` has a `p`-Sylow `P ⊆ V = C_D(t)` acting fixed-point-freely on `K = J(D,t)` which is
cyclic. -/
theorem section2_prop1_v3 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) :
    Work.NormalComplement.Section2Prop' := by
  intro G instG finG hSit H hH t ht htH W hWH hHn hsup p hp hpE
  haveI : Fact p.Prime := ⟨hp⟩
  -- ## 0. Elementary facts
  -- Any subgroup of `D = twoPoint H t` fixes the two distinct points `1` and `t` of `G ⧸ H`.
  have two_le : ∀ {U : Subgroup G}, U ≤ twoPoint H t → 2 ≤ (fixedPts H U).ncard := by
    intro U hU
    have h1mem : ((1 : G) : G ⧸ H) ∈ fixedPts H U := by
      rw [fixedPts]; intro u hu
      change ((u * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
      rw [QuotientGroup.eq]
      simpa using H.inv_mem (hU hu).1
    have htmem : ((t : G) : G ⧸ H) ∈ fixedPts H U := by
      rw [fixedPts]; intro u hu
      change ((u * t : G) : G ⧸ H) = ((t : G) : G ⧸ H)
      rw [QuotientGroup.eq]
      have hu2 : t⁻¹ * u * t ∈ H := by
        obtain ⟨h, hh, hhu⟩ := Subgroup.mem_map.mp (hU hu).2
        have hkey : t⁻¹ * u * t = h := by
          rw [← hhu]
          change t⁻¹ * (t * h * t⁻¹) * t = h
          group
        rw [hkey]; exact hh
      have hkey2 : (u * t)⁻¹ * t = (t⁻¹ * u * t)⁻¹ := by group
      rw [hkey2]; exact H.inv_mem hu2
    have hne : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
      intro hcon
      rw [QuotientGroup.eq] at hcon
      exact htH (by simpa using hcon)
    have hsub : (insert ((1 : G) : G ⧸ H) {((t : G) : G ⧸ H)} : Set (G ⧸ H)) ⊆ fixedPts H U := by
      intro ω hω
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
      rcases hω with rfl | rfl
      · exact h1mem
      · exact htmem
    have hcard : (insert ((1 : G) : G ⧸ H) {((t : G) : G ⧸ H)} : Set (G ⧸ H)).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by simpa using hne), Set.ncard_singleton]
    have := Set.ncard_le_ncard hsub
    omega
  -- Conjugation unfolds on the coset space as `(d u d⁻¹) • ω = d • (u • (d⁻¹ • ω))`.
  have smul_conj : ∀ (d u : G) (ω : G ⧸ H),
      (MulAut.conj d).toMonoidHom u • ω = d • (u • (d⁻¹ • ω)) := by
    intro d u ω
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mul_smul, mul_smul]
  -- `ω ↦ d⁻¹ • ω` is a bijection from the fixed points of `U^d` onto those of `U`.
  have ncard_fixedPts_conj : ∀ (U : Subgroup G) (d : G),
      (fixedPts H (U.map (MulAut.conj d).toMonoidHom)).ncard = (fixedPts H U).ncard := by
    intro U d
    refine Set.ncard_congr (fun ω (_ : ω ∈ fixedPts H (U.map (MulAut.conj d).toMonoidHom)) =>
      d⁻¹ • ω) ?_ ?_ ?_
    · intro ω hω u hu
      have hmem : (MulAut.conj d).toMonoidHom u ∈ U.map (MulAut.conj d).toMonoidHom :=
        ⟨u, hu, rfl⟩
      have h := hω _ hmem
      rw [smul_conj d u ω] at h
      calc u • (d⁻¹ • ω) = d⁻¹ • (d • (u • (d⁻¹ • ω))) := by rw [inv_smul_smul]
        _ = d⁻¹ • ω := by rw [h]
    · intro a _ b _ hab
      have h := congrArg (fun ω => d • ω) hab
      simpa only [smul_inv_smul] using h
    · intro ω hω
      refine ⟨d • ω, ?_, ?_⟩
      · intro x hx
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
        rw [smul_conj d u (d • ω), inv_smul_smul, hω u hu]
      · rw [inv_smul_smul]
  have fix_mono : ∀ {A B : Subgroup G}, A ≤ B → fixedPts H B ⊆ fixedPts H A :=
    fun h ω hω x hx => hω x (h hx)
  -- ## 1. a `p`-Sylow `P₀` of `E = W ⊓ D`
  obtain ⟨P₀, -, hP₀syl⟩ :=
    aux_exists_isSylowIn_ge (p := p) (T := ⊥) (X := W ⊓ twoPoint H t) bot_le
      (IsPGroup.of_bot (p := p))
  have hP₀E : P₀ ≤ W ⊓ twoPoint H t := hP₀syl.2.1
  have hP₀p : IsPGroup p P₀ := hP₀syl.1
  -- ## 2. Helpers
  -- `O_{p'}(C_W(U)) ≤ N_W(U)`, the trivial half of every normaliser identity below.
  have pPrimeCore_le : ∀ U : Subgroup G,
      pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ≤
        Subgroup.normalizer (U : Set G) ⊓ W :=
    fun U => (Subgroup.map_subtype_le _).trans
      (inf_le_inf (Subgroup.centralizer_le_normalizer (s := (U : Set G))) (le_refl W))
  have le_eq : ∀ U : Subgroup G,
      pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ twoPoint H t)) ≤
      Subgroup.normalizer (U : Set G) ⊓ W :=
    fun U => sup_le (pPrimeCore_le U) (inf_le_inf_left _ inf_le_left)
  -- Case 1: two fixed points.
  have eq_of_le1 : ∀ {U : Subgroup G}, U ≤ W ⊓ twoPoint H t → (fixedPts H U).ncard = 2 →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ twoPoint H t)) := by
    intro U hUE h2
    have hle := case1_normalizer_le G hH ht htH hWH hUE h2
    have hNE : Subgroup.normalizer (U : Set G) ⊓ (W ⊓ twoPoint H t) =
        Subgroup.normalizer (U : Set G) ⊓ W :=
      le_antisymm (inf_le_inf_left _ inf_le_left) (le_inf inf_le_left hle)
    rw [hNE]
    exact (sup_eq_right.mpr (pPrimeCore_le U)).symm
  -- Case 2, for a subgroup `U` that already lies in `V = centD H t`.
  have eq_of_case2V : ∀ {U : Subgroup G}, U ≤ W ⊓ twoPoint H t → IsPGroup p U →
      U ≤ centD H t → 3 ≤ (fixedPts H U).ncard →
      (∃ U₁ : Subgroup G, U₁ ≤ U ∧ U₁ ≠ ⊥ ∧
        ∃ k ∈ Kset (twoPoint H t) t, k ≠ 1 ∧ ∀ u ∈ U₁, k * u = u * k) →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ twoPoint H t)) := by
    intro U hUE hUp hUV h3 hcase2
    exact le_antisymm
      (case2_normalizer_le_v3 G hSit hBP hC4 hP3 hH ht htH hWH hHn hsup hUV
        (hUE.trans inf_le_left) hp hUp h3 hcase2)
      (le_eq U)
  -- Failure of fixed-point-freeness on `K` produces the case-2 witness.
  have key : ∀ {U : Subgroup G},
      ¬ (∀ x ∈ U, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) →
      ∃ U₁ : Subgroup G, U₁ ≤ U ∧ U₁ ≠ ⊥ ∧
        ∃ k ∈ Kset (twoPoint H t) t, k ≠ 1 ∧ ∀ u ∈ U₁, k * u = u * k := by
    intro U hnf
    push_neg at hnf
    obtain ⟨x, hxU, hx1, k, hkK, hkx, hk1⟩ := hnf
    refine ⟨Subgroup.zpowers x, Subgroup.zpowers_le.mpr hxU, ?_, k, hkK, hk1, ?_⟩
    · rw [Subgroup.zpowers_ne_bot]; exact hx1
    · have hxk : x * k = k * x := by
        have h := congrArg (fun y => y * x) hkx
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
      intro u hu
      have hmem : u ∈ Subgroup.centralizer ({k} : Set G) :=
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxk)) hu
      exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
  -- A fixed-point-free `p`-subgroup of `V` is cyclic (App. I (5)(c)).
  have cyclicV : ∀ {U : Subgroup G}, U ≤ centD H t → IsPGroup p U → U ≠ ⊥ →
      (∀ x ∈ U, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) →
      IsCyclic U :=
    fun hUV hUp hne hf => cyclic_of_fpf_on_centD hSit hH ht htH hFT hp hUV hUp hne hf
  -- ## 3. The case split on `P₀`
  by_cases h2fix : (fixedPts H P₀).ncard = 2
  · -- ### Case I: `P₀` fixes exactly the two points `1` and `t`
    refine Or.inl ?_
    refine pcontrol_prod_v2 (p := p) (E := W ⊓ twoPoint H t) (W := W)
      inf_le_left hpE hP₀syl (eq_of_le1 hP₀E h2fix) ?_
    intro U hUP hUnotcyc
    have hUE : U ≤ W ⊓ twoPoint H t := hUP.trans hP₀E
    have hUp : IsPGroup p U := hP₀p.to_le hUP
    rcases eq_or_lt_of_le (two_le (hUE.trans inf_le_right)) with h2eq | h2lt
    · exact eq_of_le1 hUE h2eq.symm
    · -- `U` is non-cyclic and has `≥ 3` fixed points: conjugate it into `V` and use case 2 there.
      have h3 : 3 ≤ (fixedPts H U).ncard := by omega
      obtain ⟨d, hdD, hdU⟩ := prop2b_conj_into_centD G hSit hBP hC4 hH ht htH
        (hUE.trans inf_le_right) h3
      have hUne : U ≠ ⊥ := fun h => hUnotcyc (by rw [h]; infer_instance)
      have hU'dne : U.map (MulAut.conj d).toMonoidHom ≠ ⊥ := fun h =>
        hUne ((Subgroup.map_eq_bot_iff_of_injective U (MulAut.conj d).injective).mp h)
      have hU'nc : ¬ IsCyclic (U.map (MulAut.conj d).toMonoidHom : Subgroup G) := fun hc =>
        hUnotcyc ((aux_isCyclic_map_conj_iff U d).mpr hc)
      have hWfix : W.map (MulAut.conj d).toMonoidHom = W :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHn hdD.1)
      have hDfix : (twoPoint H t).map (MulAut.conj d).toMonoidHom = twoPoint H t :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hdD)
      have hU'E : U.map (MulAut.conj d).toMonoidHom ≤ W ⊓ twoPoint H t :=
        le_inf
          (hWfix ▸ Subgroup.map_mono (hUE.trans inf_le_left))
          (hDfix ▸ Subgroup.map_mono (hUE.trans inf_le_right))
      have h3' : 3 ≤ (fixedPts H (U.map (MulAut.conj d).toMonoidHom)).ncard := by
        rw [ncard_fixedPts_conj U d]; exact h3
      have hnf' : ¬ (∀ x ∈ U.map (MulAut.conj d).toMonoidHom, x ≠ 1 →
          ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) := fun hf =>
        hU'nc (cyclicV hdU (hUp.map _) hU'dne hf)
      exact (normalizerCond_conj (U := U) hdD hWH hHn).mp
        (eq_of_case2V hU'E (hUp.map _) hdU h3' (key hnf'))
  · -- ### Case II: `P₀` fixes at least three points; conjugate it into `V`
    have h2le : 2 ≤ (fixedPts H P₀).ncard := two_le (hP₀E.trans inf_le_right)
    have h3₀ : 3 ≤ (fixedPts H P₀).ncard := by omega
    obtain ⟨d, hdD, hdP₀⟩ := prop2b_conj_into_centD G hSit hBP hC4 hH ht htH
      (hP₀E.trans inf_le_right) h3₀
    set P : Subgroup G := P₀.map (MulAut.conj d).toMonoidHom with hPdef
    have hPV : P ≤ centD H t := hdP₀
    have hPp : IsPGroup p P := hP₀p.map _
    have h3P : 3 ≤ (fixedPts H P).ncard := by
      rw [hPdef, ncard_fixedPts_conj P₀ d]; exact h3₀
    have hWfix : W.map (MulAut.conj d).toMonoidHom = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHn hdD.1)
    have hDfix : (twoPoint H t).map (MulAut.conj d).toMonoidHom = twoPoint H t :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hdD)
    have hEfix : (W ⊓ twoPoint H t).map (MulAut.conj d).toMonoidHom = W ⊓ twoPoint H t := by
      rw [Subgroup.map_inf W (twoPoint H t) (MulAut.conj d).toMonoidHom
        (MulAut.conj d).injective, hWfix, hDfix]
    have hPsyl : IsSylowIn p P (W ⊓ twoPoint H t) := by
      have h := aux_isSylowIn_map_conj hP₀syl d
      rwa [hEfix] at h
    have hPE : P ≤ W ⊓ twoPoint H t := hPsyl.2.1
    -- `P ≠ ⊥`: it is a Sylow of `E` and `p ∣ |E|`.
    have hPne : P ≠ ⊥ := by
      have hpP : p ∣ Nat.card ↥P := by
        have hE : Nat.card ↥(W ⊓ twoPoint H t) =
            (P.subgroupOf (W ⊓ twoPoint H t)).index * Nat.card ↥P := by
          rw [← Subgroup.index_mul_card (P.subgroupOf (W ⊓ twoPoint H t)),
            aux_card_subgroupOf_eq P (W ⊓ twoPoint H t) hPE]
        rw [hE] at hpE
        exact (hp.dvd_mul.mp hpE).resolve_left hPsyl.2.2
      intro hbot
      rw [hbot] at hpP
      have h1 : Nat.card ↥(⊥ : Subgroup G) = 1 := by simp
      rw [h1] at hpP
      exact hp.ne_one (Nat.dvd_one.mp hpP)
    by_cases hfpfP : ∀ x ∈ P, x ≠ 1 → ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1
    · -- `P ≤ V` is fixed-point-free on `K`, hence cyclic: the second alternative.
      exact Or.inr ⟨P, hPsyl, hPV, hfpfP, cyclicV hPV hPp hPne hfpfP⟩
    · -- Otherwise the two normaliser hypotheses of the `p`-control criterion hold.
      refine Or.inl ?_
      refine pcontrol_prod_v2 (p := p) (E := W ⊓ twoPoint H t) (W := W) inf_le_left hpE hPsyl
        (eq_of_case2V hPE hPp hPV h3P (key hfpfP)) ?_
      intro U hUP hUnotcyc
      have hUE : U ≤ W ⊓ twoPoint H t := hUP.trans hPE
      have hUp : IsPGroup p U := hPp.to_le hUP
      have hUV : U ≤ centD H t := hUP.trans hPV
      have h3U : 3 ≤ (fixedPts H U).ncard :=
        le_trans h3P (Set.ncard_le_ncard (fix_mono hUP))
      have hnfU : ¬ (∀ x ∈ U, x ≠ 1 →
          ∀ k ∈ Kset (twoPoint H t) t, x * k * x⁻¹ = k → k = 1) := fun hf =>
        hUnotcyc (cyclicV hUV hUp (fun h => hUnotcyc (by rw [h]; infer_instance)) hf)
      exact eq_of_case2V hUE hUp hUV h3U (key hnfU)

end Work.NormalComplement
