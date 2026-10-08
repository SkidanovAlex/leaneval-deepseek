import Submission.Work.AppXIDickson.Defs
import Submission.Work.AppXIDickson.card_eq_one_of_dickson
import Submission.Work.AppXIDickson.cq_noncomm_structure
import Submission.Work.AppXIDickson.field_of_free_comm_action
import Submission.Work.AppXIDickson.nearField_quotient_data
import Submission.Work.AppXIDickson.dickson_step
import Submission.Work.S3.cq_ell_subgroup_isCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIDickson.AppXI2` — Appendix XI Prop. 2, i.e. `AppXIProp2` (BS pass 17, Brief 6)

**Deliverable.** `Work.AppXIDickson.appXIProp2_of`:

```
appXIProp2_of (hNFp : NearFieldAppXIPropPlus) (hFT) (hC4) (hTh) (hHig) : AppXIProp2
```

i.e. in the standing context of Peterfalvi II Ch. V §3 (Théorème F), a non-abelian `C_Q(P)` has
order `8` — the input `AppXIProp2` of step (5) (`Work.ThmF.ChV3.AppXIProp2`, consumed by
`Work.ThmF.Prove.step5` and hence by `Work.ThmF.ChV3.chain15`).

The proof is the Dickson route of App. XI Prop. 2:

* `cq_noncomm_structure` (B2) gives `x, y ∈ C_Q(P)` and a central odd `C ≤ C_Q(P)` with
  `x⁴ = 1`, `y x y⁻¹ = x⁻¹`, `A := ⟨x⟩ ⊔ C` cyclic of order `4|C|` and `|C_Q(P)| = 8|C|`;
* `nearField_quotient_data` builds the near-field quotient `V = R/N` of App. XI Prop. 1 as a
  finite abelian group of order `|C_Q(P)| + 1 = 8|C| + 1` on which `C_Q(P)` acts
  fixed-point-freely;
* `dickson_step` applies `field_of_free_comm_action` (L0: `V` is the additive group of a finite
  field `K` with `A ↪ Kˣ`) and `card_eq_one_of_dickson` (B1: an involutive field automorphism
  with a fixed subgroup `C'` of odd order and `|K| = 8|C'| + 1` forces `|C'| = 1`) to the
  involution `σ_y` of `K` induced by `y`, giving `|C| = 1` and hence `|C_Q(P)| = 8`.

Note `S = Additive (↥R ⧸ N.subgroupOf R)` is *not* needed at this level: only its "abstract
shadow" (the action and the cardinality) is consumed, which is what `nearField_quotient_data`
provides.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.AppXIDickson

open Work.ThmF.ChV3

theorem appXIProp2_of (hNFp : NearFieldAppXIPropPlus) (hFT : FeitThompsonProp)
    (hC4 : ChIIFourProp) (hTh : ThompsonFrobeniusProp) (hHig : HigmanProp) : AppXIProp2 := by
  intro G _ _ H Q t s r P c hnc
  classical
  -- ## step (2): the near-field shadow
  have hNF : NearFieldAppXIProp := hNFp.toShadow
  obtain ⟨m, R, N, hN, hm, hprime, hNR, hRc, hRn, hNn, hRcard, hcq, hfpf, hcommR⟩ :=
    hNFp G H Q t s r P c
  -- ## B2: the structure of the non-abelian `C_Q(P)`
  obtain ⟨x, y, C0, hxCQ, hyCQ, hC0CQ, hxord, hyx, hC0odd, hC0cent, hAcyc, hA0card, hCQcard⟩ :=
    cq_noncomm_structure hFT hC4 hTh hNF hHig c hnc
  -- ## the near-field quotient `V = R/N` with its `C_Q(P)`-action
  obtain ⟨V, hVadd, hVfin, hVsmul, hVcard, hVfpf⟩ :=
    nearField_quotient_data (R := R) (N := N) (f := orderOf (s * t)) (m := m) c hN hNR hRn hNn
      hRcard hcq hfpf hcommR
  letI := hVadd
  letI := hVfin
  letI := hVsmul
  -- ## `A = ⟨x⟩ ⊔ C`, `B = ⟨y⟩`
  set A : Subgroup G := Subgroup.zpowers x ⊔ C0 with hAdef
  set B : Subgroup G := Subgroup.zpowers y with hBdef
  have hxA : x ∈ A := by rw [hAdef]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyB : y ∈ B := by rw [hBdef]; exact Subgroup.mem_zpowers y
  have hCA : C0 ≤ A := by rw [hAdef]; exact le_sup_right
  have hA_le : A ≤ CQ Q P := by
    rw [hAdef]; exact sup_le (Subgroup.zpowers_le.mpr hxCQ) hC0CQ
  have hB_le : B ≤ CQ Q P := by rw [hBdef]; exact Subgroup.zpowers_le.mpr hyCQ
  -- `A` is cyclic, hence abelian (`CommGroup ↥A` is what L0 consumes); it is built as a
  -- structure extension of the ambient `Group ↥A` so that the underlying `Mul` is the ambient one
  haveI hAcycI : IsCyclic ↥A := hAcyc
  letI hAcomm : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with
      mul_comm := fun u v => by
        obtain ⟨g, hg⟩ := hAcycI.exists_generator
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg v)
        exact zpow_mul_comm g i j }
  letI : DistribMulAction ↥A V := DistribMulAction.compHom V (Subgroup.inclusion hA_le)
  letI : DistribMulAction ↥B V := DistribMulAction.compHom V (Subgroup.inclusion hB_le)
  -- ## `y` normalises `A = ⟨x⟩ ⊔ C`
  have hyx_inv : y * x = x⁻¹ * y := by
    have h := congrArg (fun t : G => t * y) hyx
    simpa [mul_assoc] using h
  have hyx_inv' : y * x⁻¹ = x * y := by
    have h4 : y * x⁻¹ * y⁻¹ = x := by
      have h := congrArg Inv.inv hyx
      simpa [mul_assoc] using h
    have h := congrArg (fun t : G => t * y) h4
    simpa [mul_assoc] using h
  have hconj_x : ∀ k : ℤ, y * x ^ k * y⁻¹ = (x⁻¹) ^ k := by
    intro k
    calc y * x ^ k * y⁻¹ = (MulAut.conj y) (x ^ k) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj y) x) ^ k := map_zpow (MulAut.conj y) x k
      _ = (x⁻¹) ^ k := by rw [MulAut.conj_apply, hyx]
  have hsl_conj : ∀ z ∈ Subgroup.zpowers x, y * z * y⁻¹ ∈ Subgroup.zpowers x := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-k, ?_⟩
    rw [hconj_x k, inv_zpow, zpow_neg]
  have hsC_conj : ∀ z ∈ C0, y * z * y⁻¹ ∈ C0 := by
    intro z hz
    have h := hC0cent z hz y hyCQ
    rw [← h, mul_inv_cancel_right]
    exact hz
  have hmapA_le : Subgroup.map (MulAut.conj y).toMonoidHom A ≤ A := by
    rw [hAdef, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      exact Subgroup.mem_sup_left (hsl_conj w hw)
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      exact Subgroup.mem_sup_right (hsC_conj w hw)
  have hmapA : Subgroup.map (MulAut.conj y).toMonoidHom A = A := by
    refine Subgroup.eq_of_le_of_card_ge hmapA_le ?_
    rw [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj y))]
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 : (MulAut.conj y) a ∈ Subgroup.map (MulAut.conj y).toMonoidHom A :=
        Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      rw [hmapA] at h1
      simpa [MulAut.conj_apply] using h1
    · intro hya
      have h1 : y * a * y⁻¹ ∈ Subgroup.map (MulAut.conj y).toMonoidHom A := by rw [hmapA]; exact hya
      obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp h1
      have h2 : w = a := by
        apply MulEquiv.injective (MulAut.conj y)
        rw [MulAut.conj_apply]
        have h3 : y * w * y⁻¹ = y * a * y⁻¹ := hw'
        rw [h3, MulAut.conj_apply]
      rwa [h2] at hw
  have hB_N : B ≤ Subgroup.normalizer (A : Set G) := by
    rw [hBdef]; exact Subgroup.zpowers_le.mpr hyN
  let φ : ↥B →* MulAut ↥A := (Work.S3.CQEll.conjAutHom A).comp (Subgroup.inclusion hB_N)
  have hφ_val : ∀ (b : ↥B) (a : ↥A), ((φ b a : ↥A) : G) = (b : G) * (a : G) * (b : G)⁻¹ :=
    fun b a => rfl
  have hsmulA : ∀ (a : ↥A) (v : V), a • v = (Subgroup.inclusion hA_le a) • v :=
    fun a v => rfl
  have hsmulB : ∀ (b : ↥B) (v : V), b • v = (Subgroup.inclusion hB_le b) • v :=
    fun b v => rfl
  -- ## the hypotheses of `dickson_step`
  have hcompat : ∀ (b : ↥B) (a : ↥A) (v : V), b • (a • v) = (φ b a) • (b • v) := by
    intro b a v
    have hkey : Subgroup.inclusion hA_le (φ b a) * Subgroup.inclusion hB_le b
        = Subgroup.inclusion hB_le b * Subgroup.inclusion hA_le a := by
      apply Subtype.ext
      show (b : G) * (a : G) * (b : G)⁻¹ * (b : G) = (b : G) * (a : G)
      group
    calc b • (a • v)
        = (Subgroup.inclusion hB_le b) • ((Subgroup.inclusion hA_le a) • v) := by
          rw [hsmulB b, hsmulA a]
      _ = (Subgroup.inclusion hB_le b * Subgroup.inclusion hA_le a) • v :=
          (mul_smul _ _ _).symm
      _ = (Subgroup.inclusion hA_le (φ b a) * Subgroup.inclusion hB_le b) • v := by rw [hkey]
      _ = (Subgroup.inclusion hA_le (φ b a)) • ((Subgroup.inclusion hB_le b) • v) :=
          mul_smul _ _ _
      _ = (φ b a) • (b • v) := by
          rw [hsmulA (φ b a) (b • v), hsmulB b v]
  have hfree : ∀ (a : ↥A) (v : V), v ≠ 0 → a • v = v → a = 1 := by
    intro a v hv hv'
    have h1 : Subgroup.inclusion hA_le a = 1 := by
      by_contra hne
      exact hv (hVfpf (Subgroup.inclusion hA_le a) hne v (by rwa [hsmulA a v] at hv'))
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  have hA0 : Nat.card ↥A = 4 * Nat.card ↥C0 := by rw [hAdef]; exact hA0card
  have hbig : Nat.card V ≤ 2 * Nat.card ↥A + 1 := by
    rw [hVcard, ← hcq, hCQcard, hA0]
    omega
  -- `y²` centralises `A`
  have hyy_cx : x * (y * y) = (y * y) * x := by
    rw [show (y * y) * x = y * (y * x) from by group, hyx_inv,
      show y * (x⁻¹ * y) = (y * x⁻¹) * y from by group, hyx_inv',
      show (x * y) * y = x * (y * y) from by group]
  have hyy_cC : ∀ c ∈ C0, c * (y * y) = (y * y) * c := by
    intro c hc
    have h := hC0cent c hc y hyCQ
    rw [show (y * y) * c = y * (y * c) from by group, ← h,
      show y * (c * y) = (y * c) * y from by group, ← h,
      show (c * y) * y = c * (y * y) from by group]
  have hA_cent : A ≤ Subgroup.centralizer ({(y * y)} : Set G) := by
    rw [hAdef]
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyy_cx
    · intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyy_cC c hc
  have hy2' : φ ⟨y, hyB⟩ * φ ⟨y, hyB⟩ = 1 := by
    refine MulEquiv.ext fun a => ?_
    rw [MulAut.mul_apply, MulAut.one_apply]
    apply Subtype.ext
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hA_cent a.2)
    rw [hφ_val ⟨y, hyB⟩ ((φ ⟨y, hyB⟩) a), hφ_val ⟨y, hyB⟩ a,
      show y * (y * (a : G) * y⁻¹) * y⁻¹ = (y * y) * (a : G) * (y * y)⁻¹ from by group,
      ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hy2 : φ (⟨y, hyB⟩ * ⟨y, hyB⟩) = 1 := by rw [map_mul, hy2']
  have hxne : x ≠ x⁻¹ := by
    intro h
    have h2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h]
      exact mul_inv_cancel x
    have h3 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hxord] at h3
    omega
  have hyne : φ ⟨y, hyB⟩ ≠ 1 := by
    intro h
    have h1 : ((φ ⟨y, hyB⟩ ⟨x, hxA⟩ : ↥A) : G) = x := by
      have h' := congrArg (fun (f : MulAut ↥A) => ((f ⟨x, hxA⟩ : ↥A) : G)) h
      simpa using h'
    rw [hφ_val ⟨y, hyB⟩ ⟨x, hxA⟩, hyx] at h1
    exact hxne h1.symm
  have hcard_sub : Nat.card ↥(C0.subgroupOf A) = Nat.card ↥C0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
  have hCodd' : Odd (Nat.card ↥(C0.subgroupOf A)) := by rw [hcard_sub]; exact hC0odd
  have hcardV : Nat.card V = 8 * Nat.card ↥(C0.subgroupOf A) + 1 := by
    rw [hcard_sub, hVcard, ← hcq, hCQcard]
  have hCfix : ∀ c ∈ C0.subgroupOf A, φ ⟨y, hyB⟩ c = c := by
    intro c hc
    have hcC : (c : G) ∈ C0 := Subgroup.mem_subgroupOf.mp hc
    apply Subtype.ext
    rw [hφ_val ⟨y, hyB⟩ c]
    have h := hC0cent (c : G) hcC y hyCQ
    rw [← h]; group
  -- ## the Dickson step
  have hC1 : Nat.card ↥(C0.subgroupOf A) = 1 :=
    dickson_step (V := V) (A := ↥A) (B := ↥B) φ hcompat hfree hbig ⟨y, hyB⟩ hy2 hyne
      (C0.subgroupOf A) hCodd' hCfix hcardV
  have hC0card1 : Nat.card ↥C0 = 1 := by rw [← hcard_sub]; exact hC1
  rw [hCQcard, hC0card1, mul_one]

end Work.AppXIDickson
