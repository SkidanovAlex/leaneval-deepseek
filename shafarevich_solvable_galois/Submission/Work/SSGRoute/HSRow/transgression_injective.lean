import Mathlib
import Submission.Work.SSGRoute.HSConj
import Submission.Work.SSGRoute.HSRestrict
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.HS.Basic
import Submission.Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
import Submission.Work.SSGRoute.HSRow.normC_mem_lcCocycles2
import Submission.Work.SSGRoute.HSRow.normC_coboundary
import Submission.Work.SSGRoute.HSRow.tprim_primitive
import Submission.Work.SSGRoute.HSRow.tcoch_isLocConstOn
import Submission.Work.SSGRoute.HSRow.exists_linear_primitive
import Submission.Work.SSGRoute.HSRow.tcoch_mem_range_conj1_of_coboundary
import Submission.Work.SSGRoute.HSRow.tcoch_gauge_shift
import Submission.Work.SSGRoute.HSRow.exists_coboundary_of_gauge
import Submission.Work.SSGRoute.HSRow.exists_chi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

open scoped Pointwise
open Classical

noncomputable section

section Helpers

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

section Linearity

lemma tcoch_add_pair (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β β' : (Ω ≃ₐ[k] Ω) → M) :
    tcoch p k Ω K M I σ (c + c') (β + β')
      = tcoch p k Ω K M I σ c β + tcoch p k Ω K M I σ c' β' := by
  funext x
  by_cases hx : x ∈ I
  · simp only [Pi.add_apply, tcoch_apply_of_mem p k Ω K M I σ (c + c') (β + β') hx,
      tcoch_apply_of_mem p k Ω K M I σ c β hx,
      tcoch_apply_of_mem p k Ω K M I σ c' β' hx,
      tprim_apply, smul_add]
    abel
  · simp only [Pi.add_apply, tcoch_apply_of_not_mem p k Ω K M I σ (c + c') (β + β') hx,
      tcoch_apply_of_not_mem p k Ω K M I σ c β hx,
      tcoch_apply_of_not_mem p k Ω K M I σ c' β' hx, add_zero]

lemma tcoch_smul_pair (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M) (a : ZMod p) :
    tcoch p k Ω K M I σ (a • c) (a • β) = a • tcoch p k Ω K M I σ c β := by
  funext x
  by_cases hx : x ∈ I
  · rw [Pi.smul_apply]
    simp only [tcoch_apply_of_mem p k Ω K M I σ (a • c) (a • β) hx,
      tcoch_apply_of_mem p k Ω K M I σ c β hx,
      tprim_apply, Pi.smul_apply, smul_sub, smul_add]
    try rw [smul_comm (SSGRoute.res k K σ) a (β (σ⁻¹ * x * σ))]
    try rw [smul_comm (SSGRoute.res k K x) a (c σ σ⁻¹)]
    try abel
  · simp only [Pi.smul_apply, tcoch_apply_of_not_mem p k Ω K M I σ (a • c) (a • β) hx,
      tcoch_apply_of_not_mem p k Ω K M I σ c β hx, smul_zero]

end Linearity

section Assembly

variable (A₀ : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)

theorem exists_injective_of_pieces
    (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (hprim : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M),
      c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀) →
      SSGRoute.IsLocConstOn I β →
      (∀ n ∈ I, ∀ m ∈ I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m) →
      ∀ n ∈ I, ∀ m ∈ I,
        SSGRoute.res k K n • tprim p k Ω K M σ c β m - tprim p k Ω K M σ c β (n * m)
          + tprim p k Ω K M σ c β n = c n m)
    (htlc : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M),
      c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀) →
      SSGRoute.IsLocConstOn I β →
      SSGRoute.IsLocConstOn I (tcoch p k Ω K M I σ c β))
    (hκ : ∃ κ : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)) →ₗ[ZMod p]
        ↥(lcOneCoins p k Ω K M I),
      ∀ (c : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)))
        (n m : Ω ≃ₐ[k] Ω), n ∈ I → m ∈ I →
        SSGRoute.res k K n • (κ c).1 m - (κ c).1 (n * m) + (κ c).1 n = c.1 n m)
    (hP6 : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M),
      c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀) →
      c ∈ Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀) → c 1 1 = 0 →
      SSGRoute.IsLocConstOn I β →
      (∀ n ∈ I, ∀ m ∈ I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m) →
      tcoch p k Ω K M I σ c β ∈ Work.SSGRoute.lcCocycles p k Ω K M I →
      Work.SSGRoute.toClass p k Ω K M I (tcoch p k Ω K M I σ c β) ∈
        LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id))
    (hP7 : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M),
      c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀) →
      SSGRoute.IsLocConstOn I β →
      (∀ n ∈ I, ∀ m ∈ I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m) →
      tcoch p k Ω K M I σ c β ∈ Work.SSGRoute.lcCocycles p k Ω K M I →
      Work.SSGRoute.toClass p k Ω K M I (tcoch p k Ω K M I σ c β) ∈
        LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id) →
      ∃ (β' : (Ω ≃ₐ[k] Ω) → M) (m : M),
        SSGRoute.IsLocConstOn I β' ∧
        (∀ n ∈ I, ∀ m' ∈ I, SSGRoute.res k K n • β' m' - β' (n * m') + β' n = c n m') ∧
        (∀ n ∈ I, tprim p k Ω K M σ c β' n - β' n = SSGRoute.res k K n • m - m))
    (hcore : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M) (m : M)
        (χ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) → M),
      c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀) → c 1 1 = 0 →
      SSGRoute.IsLocConstOn I β →
      (∀ n ∈ I, ∀ m' ∈ I, SSGRoute.res k K n • β m' - β (n * m') + β n = c n m') →
      (∀ n ∈ I, tprim p k Ω K M σ c β n - β n = SSGRoute.res k K n • m - m) →
      SSGRoute.IsLocConstOn ⊤ χ →
      (∀ γ δ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
        χ (γ * δ) = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ
          + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω)) →
      χ ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩ = -m →
      c ∈ Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀))
    (hχ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M),
      c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀) → ∀ m : M,
      ∃ χ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) → M,
        SSGRoute.IsLocConstOn ⊤ χ ∧
        (∀ γ δ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
          χ (γ * δ) = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ
            + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω)) ∧
        χ ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩ = -m) :
    ∃ Φ : Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A₀) →ₗ[ZMod p]
        (Work.SSGRoute.H1loc p k Ω K M I ⧸
          LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)),
      Function.Injective Φ := by
  classical
  obtain ⟨κ, hκp⟩ := hκ
  let ncEnd : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)) →ₗ[ZMod p]
      ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)) :=
    { toFun := fun c => ⟨normC p k Ω K M c.1,
        normC_mem_lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀) c.1 c.2⟩
      map_add' := fun c c' => by
        apply Subtype.ext
        funext g h
        show normC p k Ω K M (c + c').1 g h
          = normC p k Ω K M c.1 g h + normC p k Ω K M c'.1 g h
        rw [normC_apply, normC_apply, normC_apply,
          show (c + c').1 = c.1 + c'.1 from rfl]
        simp only [Pi.add_apply, smul_add]
        abel
      map_smul' := fun a c => by
        apply Subtype.ext
        funext g h
        show normC p k Ω K M (a • c).1 g h = (a • normC p k Ω K M c.1) g h
        simp only [normC_apply, Pi.smul_apply, show (a • c).1 = a • c.1 from rfl]
        rw [smul_comm (SSGRoute.res k K g) a (c.1 1 1), smul_sub] }
  let tcochLin : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)) →ₗ[ZMod p]
      ((Ω ≃ₐ[k] Ω) → M) :=
    { toFun := fun c => tcoch p k Ω K M I σ c.1 (κ c).1
      map_add' := fun c c' => by
        show tcoch p k Ω K M I σ (c + c').1 (κ (c + c')).1
          = tcoch p k Ω K M I σ c.1 (κ c).1 + tcoch p k Ω K M I σ c'.1 (κ c').1
        rw [show (c + c').1 = c.1 + c'.1 from rfl, map_add,
          show (κ c + κ c').1 = (κ c).1 + (κ c').1 from rfl]
        exact tcoch_add_pair p k Ω K M I σ c.1 c'.1 (κ c).1 (κ c').1
      map_smul' := fun a c => by
        show tcoch p k Ω K M I σ (a • c).1 (κ (a • c)).1
          = a • tcoch p k Ω K M I σ c.1 (κ c).1
        rw [show (a • c).1 = a • c.1 from rfl, map_smul,
          show (a • κ c).1 = a • (κ c).1 from rfl]
        exact tcoch_smul_pair p k Ω K M I σ c.1 (κ c).1 a }
  have hmem : ∀ x : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)),
      tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 ∈
        Work.SSGRoute.lcCocycles p k Ω K M I := by
    intro x
    refine ⟨?_, htlc (ncEnd x).1 (κ (ncEnd x)).1 (ncEnd x).2 (κ (ncEnd x)).2⟩
    intro n hn m hm
    have h1 := hprim (ncEnd x).1 (κ (ncEnd x)).1 (ncEnd x).2 (κ (ncEnd x)).2
      (fun n hn m hm => hκp (ncEnd x) n m hn hm) n hn m hm
    have h2 := hκp (ncEnd x) n m hn hm
    have hgoal : SSGRoute.res k K n • tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 m
          - tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 (n * m)
          + tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 n
        = (SSGRoute.res k K n • tprim p k Ω K M σ (ncEnd x).1 (κ (ncEnd x)).1 m
            - tprim p k Ω K M σ (ncEnd x).1 (κ (ncEnd x)).1 (n * m)
            + tprim p k Ω K M σ (ncEnd x).1 (κ (ncEnd x)).1 n)
          - (SSGRoute.res k K n • (κ (ncEnd x)).1 m - (κ (ncEnd x)).1 (n * m)
            + (κ (ncEnd x)).1 n) := by
      rw [tcoch_apply_of_mem p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 hm,
        tcoch_apply_of_mem p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 (I.mul_mem hn hm),
        tcoch_apply_of_mem p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 hn]
      rw [smul_sub]
      abel
    have key : SSGRoute.res k K n • tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 m
          - tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 (n * m)
          + tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 n = 0 := by
      rw [hgoal, h1, h2, sub_self]
    rw [← sub_eq_zero]
    have hneg : tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 (n * m)
          - (tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 n
            + SSGRoute.res k K n • tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 m)
        = -(SSGRoute.res k K n • tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 m
          - tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 (n * m)
          + tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1 n) := by abel
    rw [hneg, key, neg_zero]
  let aMap : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)) →ₗ[ZMod p]
      ↥(Work.SSGRoute.lcCocycles p k Ω K M I) := (tcochLin.comp ncEnd).codRestrict _ hmem
  have hq_of : ∀ x : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)),
      (Submodule.mkQ (Submodule.comap (Work.SSGRoute.lcCocycles p k Ω K M I).subtype
        (Work.SSGRoute.coboundaries p k Ω K M I))) (aMap x)
        = Work.SSGRoute.toClass p k Ω K M I
            (tcoch p k Ω K M I σ (ncEnd x).1 (κ (ncEnd x)).1) := by
    intro x
    rw [Work.SSGRoute.toClass, dif_pos (hmem x), Submodule.mkQ_apply]
    exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)
  let PhiTilde : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)) →ₗ[ZMod p]
      (Work.SSGRoute.H1loc p k Ω K M I ⧸
        LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) :=
    (Submodule.mkQ (LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id))).comp
      ((Submodule.mkQ (Submodule.comap (Work.SSGRoute.lcCocycles p k Ω K M I).subtype
        (Work.SSGRoute.coboundaries p k Ω K M I))).comp aMap)
  have hPhi_apply : ∀ x : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)),
      PhiTilde x
        = (Submodule.mkQ (LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)))
          ((Submodule.mkQ (Submodule.comap (Work.SSGRoute.lcCocycles p k Ω K M I).subtype
            (Work.SSGRoute.coboundaries p k Ω K M I))) (aMap x)) := fun x => rfl
  have hker : Submodule.comap (Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)).subtype
      (Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀)) ≤ LinearMap.ker PhiTilde := by
    intro x hx
    rw [Submodule.mem_comap] at hx
    rw [LinearMap.mem_ker]
    have hx2 : (ncEnd x).1 ∈ Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀) :=
      normC_coboundary p k Ω K M (SSGRoute.decomp k A₀) x.1 hx
    have hx11 : (ncEnd x).1 1 1 = 0 := by
      show normC p k Ω K M x.1 1 1 = 0
      rw [normC_apply, map_one, one_smul, sub_self]
    have hR := hP6 (ncEnd x).1 (κ (ncEnd x)).1 (ncEnd x).2 hx2 hx11
      (κ (ncEnd x)).2 (fun n hn m hm => hκp (ncEnd x) n m hn hm) (hmem x)
    show PhiTilde x = 0
    rw [hPhi_apply x, hq_of x, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id))).mpr hR
  have hinj : ∀ x : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)),
      PhiTilde x = 0 →
      x ∈ Submodule.comap (Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)).subtype
        (Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀)) := by
    intro x hx
    rw [Submodule.mem_comap]
    have hτ' : (Submodule.mkQ (Submodule.comap (Work.SSGRoute.lcCocycles p k Ω K M I).subtype
        (Work.SSGRoute.coboundaries p k Ω K M I))) (aMap x) ∈
        LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id) := by
      have h := hx
      rw [hPhi_apply x, Submodule.mkQ_apply] at h
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id))).mp h
    rw [hq_of x] at hτ'
    obtain ⟨β', m, hβ'lc, hβ'p, hm⟩ :=
      hP7 (ncEnd x).1 (κ (ncEnd x)).1 (ncEnd x).2 (κ (ncEnd x)).2
        (fun n hn m hm => hκp (ncEnd x) n m hn hm) (hmem x) hτ'
    obtain ⟨χ, hχlc, hχ1, hχσ⟩ := hχ (ncEnd x).1 (ncEnd x).2 m
    have hx11 : (ncEnd x).1 1 1 = 0 := by
      show normC p k Ω K M x.1 1 1 = 0
      rw [normC_apply, map_one, one_smul, sub_self]
    have hcob : (ncEnd x).1 ∈ Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀) :=
      hcore (ncEnd x).1 β' m χ (ncEnd x).2 hx11 hβ'lc
        (fun n hn m' hm' => hβ'p n hn m' hm') hm hχlc hχ1 hχσ
    have hsplit : x.1 = normC p k Ω K M x.1
        + (fun g _ => SSGRoute.res k K g • x.1 1 1) := by
      funext g h
      simp only [Pi.add_apply, normC_apply]
      abel
    change x.1 ∈ Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀)
    rw [hsplit]
    refine (Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀)).add_mem hcob ?_
    exact ⟨fun _ => x.1 1 1, ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩,
      fun g _ h _ => by simp⟩
  refine ⟨Submodule.liftQ (Submodule.comap
      (Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)).subtype
      (Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀))) PhiTilde hker, ?_⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (Submodule.comap (Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A₀)).subtype
      (Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A₀))) y
  rw [Submodule.mkQ_apply] at hy
  rw [Submodule.liftQ_apply] at hy
  rw [Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  exact hinj x hy

end Assembly
end Helpers

/-- The transgression `H²_loc(D_A,M) ↪ H¹_loc(I,M) ⧸ range (conj₁ - 1)`, the first half of the
degree-`2` Hochschild–Serre two-row decomposition for `D_A = I ⋊ C` (`C = closure (zpowers σ)`).
Verbatim copy of `Submission/Work/SSGRoute/HSTwoRow/transgression_injective.lean` (a stalled
`sorry`) in the namespace `Work.SSGRoute.HSRow`, retaining the hypothesis `hIclosed` that its
intended proof needs.  Companion: `Work.SSGRoute.HSRow.coker_injects_H2loc`; consumer:
`HSTwoRow/finrank_H2loc_decomp.lean` (proved, conditional on the two halves) and through it the
`μ_p`-base case of local Tate duality and the local Euler characteristic.  Useful background:
`HSTwoRow/PLAN_H2row.md` (the proof plan), `HSTwoRow/finrank_H1loc_decomp.lean` (the proved
degree-`1` analogue with the same ingredients: `Psi_eq_zero`, `exists_extension_cocycle`,
`res1_range_eq_ker_conj1`), `HSRow/Coords.lean` (continuity of the coordinates `HS.ip`/`HS.proj`),
`HSConj` (`conj1`), `HSRestrict`, `HSTwoRow/exists_zmodN_cocycle.lean`,
`HSTwoRow/exists_lcCocycleOn_zpowers_gen_eq.lean`, `HSTwoRow/toClass_eq_of_eq_on_gen.lean`,
`isCoboundary2On_top_of_procyclicGrowth`. -/
theorem transgression_injective
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω)))
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →*
        Multiplicative (ZMod n), Function.Surjective f)
    (hvan : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subsingleton (Work.SSGRoute.H2loc p k Ω K M I))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I) :
    ∃ Φ : Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A) →ₗ[ZMod p]
        (Work.SSGRoute.H1loc p k Ω K M I ⧸
          LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)),
      Function.Injective Φ := by
  classical
  have hχ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M),
      c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A) → ∀ m : M,
      ∃ χ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) → M,
        SSGRoute.IsLocConstOn ⊤ χ ∧
        (∀ γ δ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
          χ (γ * δ) = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ
            + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω)) ∧
        χ ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩ = -m := by
    intro c hc m
    have hC : Subgroup.topologicalClosure (Subgroup.zpowers σ) ≤ SSGRoute.decomp k A :=
      Work.SSGRoute.HS.CC_le_DD A σ hσ
    have hcC : SSGRoute.IsCocycle2
        ((SSGRoute.res k K).comp
          (Subgroup.subtype (Subgroup.topologicalClosure (Subgroup.zpowers σ))))
        (fun γ δ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) => c γ δ) := by
      intro γ δ ε
      exact hc.1 γ.1 (hC γ.2) δ.1 (hC δ.2) ε.1 (hC ε.2)
    have hlcC : SSGRoute.IsLocConst2
        (fun γ δ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) => c γ δ) := by
      obtain ⟨U, hUo, hU⟩ := hc.2
      refine ⟨Subgroup.comap
        (Subgroup.subtype (Subgroup.topologicalClosure (Subgroup.zpowers σ))) U, ?_, ?_⟩
      · rw [Subgroup.coe_comap]
        exact hUo.preimage continuous_subtype_val
      · intro γ δ u v hu hv
        rw [Subgroup.mem_comap] at hu hv
        exact hU γ.1 (hC γ.2) δ.1 (hC δ.2) u.1 hu v.1 hv (hC u.2) (hC v.2)
    exact exists_chi p k Ω K M σ hZ c hcC hlcC m
  exact exists_injective_of_pieces p k Ω K M A I σ hnorm1 hnorm2
    (fun c β hc hβlc hβ =>
      tprim_primitive p k Ω K M (SSGRoute.decomp k A) I σ hσ hI hnorm2 c hc.1 β hβ)
    (fun c β hc hβlc =>
      tcoch_isLocConstOn p k Ω K M (SSGRoute.decomp k A) I σ hσ hI hnorm2 c hc.2 β hβlc)
    (exists_linear_primitive p k Ω K M (SSGRoute.decomp k A) I hI hvan)
    (fun c β hc hcob hc11 hβlc hβ htcoch =>
      tcoch_mem_range_conj1_of_coboundary p k Ω K M (SSGRoute.decomp k A) I σ hσ hI hnorm1 hnorm2
        c hc hcob hc11 β hβlc hβ htcoch)
    (fun c β hc hβlc hβ htcoch hτ =>
      tcoch_gauge_shift p k Ω K M I σ hnorm1 hnorm2 c β hβlc hβ htcoch hτ)
    (fun c β m χ hc hc11 hβlc hβ hm hχlc hχ1 hχσ =>
      exists_coboundary_of_gauge p k Ω K M A I σ hI hIclosed hnorm hσ hsup hinf c hc hc11
        β hβlc hβ m hm χ hχlc hχ1 hχσ)
    hχ

end
end Work.SSGRoute.HSRow
