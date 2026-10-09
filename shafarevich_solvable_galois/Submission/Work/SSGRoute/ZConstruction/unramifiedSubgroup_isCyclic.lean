import Mathlib
import Submission.Work.SSGRoute.ZSplit.levelK_unramifiedSubgroup
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.ZConstruction.submodule_map_mkQ_eq_span_singleton
import Submission.Work.SSGRoute.ZConstruction.levelKDecomp_quotient_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open scoped Pointwise

section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

abbrev decompInf (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  SSGRoute.decomp k A ⊓ K.fixingSubgroup

set_option linter.unusedSectionVars false

lemma res_eq_one_of_mem_decompInf (A : ValuationSubring Ω) {σ : Ω ≃ₐ[k] Ω}
    (hσ : σ ∈ decompInf k Ω K A) : SSGRoute.res k K σ = 1 := by
  have hker : (SSGRoute.res k K).ker = K.fixingSubgroup := by
    simpa using (IntermediateField.restrictNormalHom_ker (E := K))
  exact MonoidHom.mem_ker.mp (by rw [hker]; exact hσ.2)

lemma lcCocycles_one (A : ValuationSubring Ω) (x : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hx : x ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (decompInf k Ω K A)) : x 1 = 0 := by
  have h := hx.1 1 (decompInf k Ω K A).one_mem 1 (decompInf k Ω K A).one_mem
  rw [mul_one, map_one, one_smul] at h
  exact (add_left_cancel (by rw [add_zero]; exact h)).symm

lemma lcCocycles_add (A : ValuationSubring Ω) (x : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hx : x ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (decompInf k Ω K A))
    {a b : Ω ≃ₐ[k] Ω} (ha : a ∈ decompInf k Ω K A) (hb : b ∈ decompInf k Ω K A) :
    x (a * b) = x a + x b := by
  have h := hx.1 a ha b hb
  rw [res_eq_one_of_mem_decompInf k Ω K A ha, one_smul] at h
  exact h

lemma lcCocycles_inv (A : ValuationSubring Ω) (x : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hx : x ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (decompInf k Ω K A))
    {a : Ω ≃ₐ[k] Ω} (ha : a ∈ decompInf k Ω K A) : x a⁻¹ = - x a := by
  have h1 : x (a * a⁻¹) = x a + x a⁻¹ :=
    lcCocycles_add p k Ω K A x hx ha ((decompInf k Ω K A).inv_mem ha)
  rw [mul_inv_cancel, lcCocycles_one p k Ω K A x hx] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

lemma lcCocycles_exists_open_vanishing (A : ValuationSubring Ω) (x : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hx : x ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (decompInf k Ω K A)) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ h ∈ decompInf k Ω K A, h ∈ U → x h = 0 := by
  obtain ⟨U, hUo, hU⟩ := hx.2
  refine ⟨U, hUo, fun h hh hhU => ?_⟩
  have h1 := hU 1 (decompInf k Ω K A).one_mem h hhU hh
  rw [one_mul, lcCocycles_one p k Ω K A x hx] at h1
  exact h1

lemma mem_coboundarySub_iff (A : ValuationSubring Ω)
    (w : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (decompInf k Ω K A))) :
    w ∈ Work.SSGRoute.ZSplit.coboundarySub p k Ω K (decompInf k Ω K A) ↔
      ∀ h ∈ decompInf k Ω K A, (w : (Ω ≃ₐ[k] Ω) → ZMod p) h = 0 := by
  rw [Work.SSGRoute.ZSplit.mem_coboundarySub]
  constructor
  · rintro ⟨m, hm⟩ h hh
    rw [hm h hh, res_eq_one_of_mem_decompInf k Ω K A hh, one_smul, sub_self]
  · intro hw
    exact ⟨0, fun h hh => by rw [hw h hh, smul_zero, sub_zero]⟩

lemma unramifiedCocycles_dependent (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (x z : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (decompInf k Ω K A)))
    (hx : x ∈ Work.SSGRoute.ZSplit.unramifiedCocycles p k Ω K A (decompInf k Ω K A))
    (hz : z ∈ Work.SSGRoute.ZSplit.unramifiedCocycles p k Ω K A (decompInf k Ω K A))
    (hne : ∃ h ∈ decompInf k Ω K A, (x : (Ω ≃ₐ[k] Ω) → ZMod p) h ≠ 0) :
    ∃ c : ZMod p, ∀ h ∈ decompInf k Ω K A,
      (z : (Ω ≃ₐ[k] Ω) → ZMod p) h = c * (x : (Ω ≃ₐ[k] Ω) → ZMod p) h := by
  classical
  let H : Subgroup (Ω ≃ₐ[k] Ω) := decompInf k Ω K A
  let xf : (Ω ≃ₐ[k] Ω) → ZMod p := (x : (Ω ≃ₐ[k] Ω) → ZMod p)
  let zf : (Ω ≃ₐ[k] Ω) → ZMod p := (z : (Ω ≃ₐ[k] Ω) → ZMod p)
  have hxL : xf ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H := x.2
  have hzL : zf ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H := z.2
  have hxI : ∀ σ ∈ H, SSGRoute.IsInertia k A σ → xf σ = 0 :=
    (Work.SSGRoute.ZSplit.mem_unramifiedCocycles p k Ω K A H x).mp hx
  have hzI : ∀ σ ∈ H, SSGRoute.IsInertia k A σ → zf σ = 0 :=
    (Work.SSGRoute.ZSplit.mem_unramifiedCocycles p k Ω K A H z).mp hz
  have hxone : xf 1 = 0 := lcCocycles_one p k Ω K A x hxL
  have hzone : zf 1 = 0 := lcCocycles_one p k Ω K A z hzL
  have hxadd : ∀ (a b : Ω ≃ₐ[k] Ω), a ∈ H → b ∈ H → xf (a * b) = xf a + xf b :=
    fun a b ha hb => lcCocycles_add p k Ω K A x hxL ha hb
  have hzadd : ∀ (a b : Ω ≃ₐ[k] Ω), a ∈ H → b ∈ H → zf (a * b) = zf a + zf b :=
    fun a b ha hb => lcCocycles_add p k Ω K A z hzL ha hb
  have hxinv : ∀ (a : Ω ≃ₐ[k] Ω), a ∈ H → xf a⁻¹ = - xf a :=
    fun a ha => lcCocycles_inv p k Ω K A x hxL ha
  have hzinv : ∀ (a : Ω ≃ₐ[k] Ω), a ∈ H → zf a⁻¹ = - zf a :=
    fun a ha => lcCocycles_inv p k Ω K A z hzL ha
  let N : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {σ | σ ∈ H ∧ xf σ = 0 ∧ zf σ = 0}
      one_mem' := ⟨H.one_mem, hxone, hzone⟩
      mul_mem' := by
        rintro a b ⟨haH, hax, haz⟩ ⟨hbH, hbx, hbz⟩
        exact ⟨H.mul_mem haH hbH, by rw [hxadd a b haH hbH, hax, hbx, add_zero],
          by rw [hzadd a b haH hbH, haz, hbz, add_zero]⟩
      inv_mem' := by
        rintro a ⟨haH, hax, haz⟩
        exact ⟨H.inv_mem haH, by rw [hxinv a haH, hax, neg_zero],
          by rw [hzinv a haH, haz, neg_zero]⟩ }
  have hNle : N ≤ H := fun σ hσ => hσ.1
  have hNnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    refine ⟨H.mul_mem (H.mul_mem hh hn.1) (H.inv_mem hh), ?_, ?_⟩
    · rw [hxadd (h * n) h⁻¹ (H.mul_mem hh hn.1) (H.inv_mem hh), hxadd h n hh hn.1,
        hn.2.1, add_zero, hxinv h hh, add_neg_cancel]
    · rw [hzadd (h * n) h⁻¹ (H.mul_mem hh hn.1) (H.inv_mem hh), hzadd h n hh hn.1,
        hn.2.2, add_zero, hzinv h hh, add_neg_cancel]
  have hNopen : ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧ V ⊓ H ≤ N := by
    obtain ⟨Ux, hUxo, hUx⟩ := lcCocycles_exists_open_vanishing p k Ω K A x hxL
    obtain ⟨Uz, hUzo, hUz⟩ := lcCocycles_exists_open_vanishing p k Ω K A z hzL
    refine ⟨Ux ⊓ Uz, ?_, ?_⟩
    · rw [Subgroup.coe_inf]; exact hUxo.inter hUzo
    · intro σ hσ
      exact ⟨hσ.2, hUx σ hσ.2 hσ.1.1, hUz σ hσ.2 hσ.1.2⟩
  have hNI : Work.SSGRoute.inertiaSub k Ω A ⊓ H ≤ N := by
    intro σ hσ
    have his : SSGRoute.IsInertia k A σ := (Work.SSGRoute.mem_inertiaSub k Ω A σ).mp hσ.1
    exact ⟨hσ.2, hxI σ hσ.2 his, hzI σ hσ.2 his⟩
  obtain ⟨g, hgH, hgen⟩ :=
    levelKDecomp_quotient_cyclic k Ω K A hA N hNle hNnorm hNopen hNI
  let xF : ↥H →* Multiplicative (ZMod p) :=
    { toFun := fun h => Multiplicative.ofAdd (xf (h : Ω ≃ₐ[k] Ω))
      map_one' := by
        show Multiplicative.ofAdd (xf ((1 : ↥H) : Ω ≃ₐ[k] Ω)) = 1
        rw [Subgroup.coe_one, hxone]; rfl
      map_mul' := by
        intro a b
        have h := hxadd (a : Ω ≃ₐ[k] Ω) (b : Ω ≃ₐ[k] Ω) a.2 b.2
        simp only [Subgroup.coe_mul, h]
        rfl }
  let zF : ↥H →* Multiplicative (ZMod p) :=
    { toFun := fun h => Multiplicative.ofAdd (zf (h : Ω ≃ₐ[k] Ω))
      map_one' := by
        show Multiplicative.ofAdd (zf ((1 : ↥H) : Ω ≃ₐ[k] Ω)) = 1
        rw [Subgroup.coe_one, hzone]; rfl
      map_mul' := by
        intro a b
        have h := hzadd (a : Ω ≃ₐ[k] Ω) (b : Ω ≃ₐ[k] Ω) a.2 b.2
        simp only [Subgroup.coe_mul, h]
        rfl }
  have xpow : ∀ m : ℤ, xf (g ^ m) = m • xf g := by
    intro m
    have h1 := map_zpow xF (⟨g, hgH⟩ : ↥H) m
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_zpow] at h2
    simpa [xF, toAdd_ofAdd, Subgroup.coe_zpow] using h2
  have zpow : ∀ m : ℤ, zf (g ^ m) = m • zf g := by
    intro m
    have h1 := map_zpow zF (⟨g, hgH⟩ : ↥H) m
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_zpow] at h2
    simpa [zF, toAdd_ofAdd, Subgroup.coe_zpow] using h2
  have hxg : xf g ≠ 0 := by
    intro h0
    obtain ⟨h₀, hh₀H, hh₀ne⟩ := hne
    obtain ⟨m, hm⟩ := hgen h₀ hh₀H
    have hx0 : xf (h₀⁻¹ * g ^ m) = 0 := hm.2.1
    have hsplit : xf (h₀⁻¹ * g ^ m) = - xf h₀ + m • xf g := by
      rw [hxadd (h₀⁻¹) (g ^ m) (H.inv_mem hh₀H) (H.zpow_mem hgH m), hxinv h₀ hh₀H, xpow m]
    rw [hsplit, h0, smul_zero, add_zero] at hx0
    exact hh₀ne (neg_eq_zero.mp hx0)
  refine ⟨zf g * (xf g)⁻¹, fun h hh => ?_⟩
  obtain ⟨m, hm⟩ := hgen h hh
  have hxm : xf h = m • xf g := by
    have hsplit : xf (h⁻¹ * g ^ m) = - xf h + m • xf g := by
      rw [hxadd (h⁻¹) (g ^ m) (H.inv_mem hh) (H.zpow_mem hgH m), hxinv h hh, xpow m]
    have hx0 : xf (h⁻¹ * g ^ m) = 0 := hm.2.1
    rw [hsplit] at hx0
    exact neg_add_eq_zero.mp hx0
  have hzm : zf h = m • zf g := by
    have hsplit : zf (h⁻¹ * g ^ m) = - zf h + m • zf g := by
      rw [hzadd (h⁻¹) (g ^ m) (H.inv_mem hh) (H.zpow_mem hgH m), hzinv h hh, zpow m]
    have hz0 : zf (h⁻¹ * g ^ m) = 0 := hm.2.2
    rw [hsplit] at hz0
    exact neg_add_eq_zero.mp hz0
  change zf h = zf g * (xf g)⁻¹ * xf h
  rw [hzm, hxm, zsmul_eq_mul, zsmul_eq_mul]
  have hc' : (zf g * (xf g)⁻¹) * (xf g) = zf g := by
    rw [mul_assoc, inv_mul_cancel₀ hxg, mul_one]
  calc (m : ZMod p) * zf g
      = (m : ZMod p) * ((zf g * (xf g)⁻¹) * (xf g)) := by rw [hc']
    _ = (zf g * (xf g)⁻¹) * ((m : ZMod p) * xf g) := by ring

end

theorem unramifiedSubgroup_isCyclic (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ u : Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) = Submodule.span (ZMod p) {u} := by
  classical
  have hkey : ∀ x ∈ Work.SSGRoute.ZSplit.unramifiedCocycles p k Ω K A (decompInf k Ω K A),
      ∀ y ∈ Work.SSGRoute.ZSplit.unramifiedCocycles p k Ω K A (decompInf k Ω K A),
      x ∉ Work.SSGRoute.ZSplit.coboundarySub p k Ω K (decompInf k Ω K A) →
      ∃ c : ZMod p, y - c • x ∈
        Work.SSGRoute.ZSplit.coboundarySub p k Ω K (decompInf k Ω K A) := by
    intro x hxUc y hyUc hxnotB
    have hne : ∃ h ∈ decompInf k Ω K A, (x : (Ω ≃ₐ[k] Ω) → ZMod p) h ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hxnotB ((mem_coboundarySub_iff p k Ω K A x).mpr (fun h hh => hcon h hh))
    obtain ⟨c, hc⟩ := unramifiedCocycles_dependent p k Ω K A hA x y hxUc hyUc hne
    refine ⟨c, ?_⟩
    rw [mem_coboundarySub_iff p k Ω K A]
    intro h hh
    have hval : ((y - c • x : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (decompInf k Ω K A))) :
        (Ω ≃ₐ[k] Ω) → ZMod p) h =
        (y : (Ω ≃ₐ[k] Ω) → ZMod p) h - c • (x : (Ω ≃ₐ[k] Ω) → ZMod p) h := by
      rw [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply]
    rw [hval, hc h hh, smul_eq_mul, sub_self]
  obtain ⟨u, hu⟩ := submodule_map_mkQ_eq_span_singleton (R := ZMod p)
    (B := Work.SSGRoute.ZSplit.coboundarySub p k Ω K (decompInf k Ω K A))
    (U := Work.SSGRoute.ZSplit.unramifiedCocycles p k Ω K A (decompInf k Ω K A)) hkey
  refine ⟨u, ?_⟩
  show Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A (decompInf k Ω K A) =
    Submodule.span (ZMod p) {u}
  simpa only [Work.SSGRoute.ZSplit.unramifiedSubgroup] using hu

end Work.SSGRoute.ZConstruction
