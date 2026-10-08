import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.conj_action_data
import Submission.Work.ThmF.ChV12.appV_regular
import Submission.Work.ThmF.ChV12.appV_semilinear

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Ch. V §1, Proposition 3 (p. 241)

`Q₀ ⋊ (D/W) ≅ (𝔽_q ⋊ 𝔽_q^*) ⋊ A`.

The involutions of `H` commute (`hcomm`), `K = J(D,t) = Kset H t` is the cyclic normal
subgroup `Ksub H t` of `D = twoPoint H t` (`hKsub`, `hKcyc`, `hKn`), and `K` acts regularly by
conjugation on `Inv(H) = Q₀ \ {1}` (`hreg`).

Then `Q₀ = Q0sub H` carries the structure of a finite field `F` (`|F| = |Q₀|`), the group
`Ksub H t` is isomorphic to `Fˣ` and acts by multiplication (App. V (a), `appV_regular`), and
`V = centD H t = C_D(t)` acts by field automorphisms with kernel `W = C_V(K)` (App. V (b),(c),
`appV_semilinear`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

namespace Work.ThmF.ChV12

open Submission.Blueprint

variable {G : Type*} [Group G]

theorem Ksub_le_H (H : Subgroup G) (t : G) : Ksub H t ≤ H :=
  fun _ hx => (Subgroup.mem_inf.mp (Ksub_le_twoPoint (H := H) t hx)).1

theorem centD_le_H (H : Subgroup G) (t : G) : centD H t ≤ H :=
  fun _ hx => (Subgroup.mem_inf.mp (centD_le_twoPoint (H := H) t hx)).1

open Classical Submission.Blueprint in theorem prop3 {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (hcomm : ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u) (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t)) (hKn : ((Work.ThmF.Ksub H t).subgroupOf (twoPoint H t)).Normal) (hreg : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), ∃! k, k ∈ Work.ThmF.Kset H t ∧ k * a * k⁻¹ = b) (s : G) (hs : s ∈ involutions (H : Set G)) (hV : centD H t = twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G)) : ∃ (F : Type) (_ : Field F) (_ : Fintype F) (e : ↥(Work.ThmF.Q0sub H) ≃* Multiplicative F) (κ : ↥(Work.ThmF.Ksub H t) ≃* Fˣ) (ρ : ↥(centD H t) →* (F ≃+* F)), Nat.card F = Nat.card ↥(Work.ThmF.Q0sub H) ∧ (∀ (k : ↥(Work.ThmF.Ksub H t)) (x : ↥(Work.ThmF.Q0sub H)) (hx : (k : G) * x * (k : G)⁻¹ ∈ Work.ThmF.Q0sub H), Multiplicative.toAdd (e ⟨(k : G) * x * (k : G)⁻¹, hx⟩) = (κ k : F) * Multiplicative.toAdd (e x)) ∧ (∀ (v : ↥(centD H t)) (x : ↥(Work.ThmF.Q0sub H)) (hx : (v : G) * x * (v : G)⁻¹ ∈ Work.ThmF.Q0sub H), Multiplicative.toAdd (e ⟨(v : G) * x * (v : G)⁻¹, hx⟩) = ρ v (Multiplicative.toAdd (e x))) ∧ ρ.ker = (Work.ThmF.W H t).subgroupOf (centD H t) := by
  -- (0) elementary facts
  obtain ⟨hQ0sq, hQ0comm, hQ0conj, hQ0inv⟩ := Q0sub_elementary H hcomm
  have hKsubH : ∀ k ∈ Ksub H t, k ∈ H :=
    fun k hk => (Subgroup.mem_inf.mp (Ksub_le_twoPoint (H := H) t hk)).1
  have hcentDH : ∀ u ∈ centD H t, u ∈ H :=
    fun u hu => (Subgroup.mem_inf.mp (centD_le_twoPoint (H := H) t hu)).1
  have hKsub_mem : ∀ x : G, x ∈ Ksub H t ↔ x ∈ Kset H t := by
    intro x
    constructor
    · intro hx
      have h' : x ∈ (Ksub H t : Set G) := hx
      rwa [hKsub] at h'
    · intro hx
      have h' : x ∈ (Ksub H t : Set G) := by rw [hKsub]; exact hx
      exact h'
  -- (1) structures
  letI : CommGroup ↥(Q0sub H) :=
    { (inferInstance : Group ↥(Q0sub H)) with
      mul_comm := fun a b => Subtype.ext (hQ0comm a.1 a.2 b.1 b.2) }
  letI : Fintype ↥(Q0sub H) := Fintype.ofFinite _
  have hKcomm : ∀ a b : ↥(Ksub H t), a * b = b * a := by
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hKcyc
    intro a b
    have ha : a ∈ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top a
    have hb : b ∈ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top b
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hm, ← hn, ← zpow_add, add_comm m n, zpow_add]
  letI : CommGroup ↥(Ksub H t) :=
    { (inferInstance : Group ↥(Ksub H t)) with mul_comm := hKcomm }
  letI : Fintype ↥(Ksub H t) := Fintype.ofFinite _
  -- (2) conjugation action data
  obtain ⟨Φ, Ψ, T, hΦ, hΨ, hT, hcompat0⟩ := conj_action_data H t hcomm hKn
  -- (3) the action of `K` on `Q₀` (multiplicative, then additive)
  letI hMDQK : MulDistribMulAction ↥(Ksub H t) ↥(Q0sub H) :=
    { smul := fun k x => Φ k x
      one_smul := by intro x; change Φ 1 x = x; rw [map_one Φ]; exact MulAut.one_apply _ x
      mul_smul := by
        intro a b x; change Φ (a * b) x = Φ a (Φ b x); rw [map_mul Φ]; rw [MulAut.mul_apply]
      smul_one := by intro a; change Φ a 1 = 1; rw [map_one (Φ a)]
      smul_mul := by intro a x y; change Φ a (x * y) = Φ a x * Φ a y; rw [map_mul (Φ a)] }
  letI hKact : DistribMulAction ↥(Ksub H t) (Additive ↥(Q0sub H)) :=
    { smul := hMDQK.smul
      one_smul := fun x => hMDQK.one_smul x
      mul_smul := fun a b x => hMDQK.mul_smul a b x
      smul_zero := fun a => hMDQK.smul_one a
      smul_add := fun a x y => hMDQK.smul_mul a x y }
  -- (4) the action of `V = centD H t` on `Q₀`
  letI hMDQU : MulDistribMulAction ↥(centD H t) ↥(Q0sub H) :=
    { smul := fun u x => Ψ u x
      one_smul := by intro x; change Ψ 1 x = x; rw [map_one Ψ]; exact MulAut.one_apply _ x
      mul_smul := by
        intro a b x; change Ψ (a * b) x = Ψ a (Ψ b x); rw [map_mul Ψ]; rw [MulAut.mul_apply]
      smul_one := by intro a; change Ψ a 1 = 1; rw [map_one (Ψ a)]
      smul_mul := by intro a x y; change Ψ a (x * y) = Ψ a x * Ψ a y; rw [map_mul (Ψ a)] }
  letI hUactQ : DistribMulAction ↥(centD H t) (Additive ↥(Q0sub H)) :=
    { smul := hMDQU.smul
      one_smul := fun x => hMDQU.one_smul x
      mul_smul := fun a b x => hMDQU.mul_smul a b x
      smul_zero := fun a => hMDQU.smul_one a
      smul_add := fun a x y => hMDQU.smul_mul a x y }
  -- (5) the action of `V` on `K`
  letI hMDUK : MulDistribMulAction ↥(centD H t) ↥(Ksub H t) :=
    { smul := fun u k => T u k
      one_smul := by intro k; change T 1 k = k; rw [map_one T]; exact MulAut.one_apply _ k
      mul_smul := by
        intro a b k; change T (a * b) k = T a (T b k); rw [map_mul T]; rw [MulAut.mul_apply]
      smul_one := by intro a; change T a 1 = 1; rw [map_one (T a)]
      smul_mul := by intro a x y; change T a (x * y) = T a x * T a y; rw [map_mul (T a)] }
  -- value lemmas for the actions
  have smulK_val : ∀ (k : ↥(Ksub H t)) (x : ↥(Q0sub H)),
      (k • Additive.ofMul x : Additive ↥(Q0sub H)) = Additive.ofMul (Φ k x) := by
    intro k x
    show Additive.ofMul (Φ k x) = Additive.ofMul (Φ k x)
    rfl
  have smulU_val : ∀ (u : ↥(centD H t)) (x : ↥(Q0sub H)),
      (u • Additive.ofMul x : Additive ↥(Q0sub H)) = Additive.ofMul (Ψ u x) := by
    intro u x
    show Additive.ofMul (Ψ u x) = Additive.ofMul (Ψ u x)
    rfl
  have smulUK_val : ∀ (u : ↥(centD H t)) (k : ↥(Ksub H t)),
      (u • k : ↥(Ksub H t)) = T u k := by
    intro u k
    show T u k = T u k
    rfl
  -- (6) compatibility
  have hcompat : ∀ (u : ↥(centD H t)) (k : ↥(Ksub H t)) (x : Additive ↥(Q0sub H)),
      u • (k • x) = (u • k) • (u • x) := by
    intro u k x
    change Additive.ofMul (Ψ u (Φ k (Additive.toMul x)))
      = Additive.ofMul (Φ (T u k) (Ψ u (Additive.toMul x)))
    rw [hcompat0 u k (Additive.toMul x)]
  -- (7) the distinguished element `s`
  have hsQ : s ∈ Q0sub H := Q0_le_Q0sub H (involutions_subset_Q0 H hs)
  have hsE : (⟨s, hsQ⟩ : ↥(Q0sub H)) ≠ 1 := by
    intro h1
    have h2 : s = 1 := congrArg Subtype.val h1
    have h3 : orderOf s = 2 := hs.2
    rw [h2] at h3
    simp at h3
  have hsE0 : (Additive.ofMul (⟨s, hsQ⟩ : ↥(Q0sub H)) : Additive ↥(Q0sub H)) ≠ 0 :=
    fun hh => hsE (show (⟨s, hsQ⟩ : ↥(Q0sub H)) = 1 from hh)
  have hUs : ∀ u : ↥(centD H t), u • (Additive.ofMul (⟨s, hsQ⟩ : ↥(Q0sub H))) =
      Additive.ofMul (⟨s, hsQ⟩ : ↥(Q0sub H)) := by
    intro u
    have hval : Ψ u (⟨s, hsQ⟩ : ↥(Q0sub H)) = ⟨s, hsQ⟩ := by
      apply Subtype.ext
      rw [hΨ u ⟨s, hsQ⟩]
      have hu : (u : G) ∈ Subgroup.centralizer ({s} : Set G) := by
        have h1 : (u : G) ∈ twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) := by
          rw [← hV]; exact u.2
        exact (Subgroup.mem_inf.mp h1).2
      have hcu : s * (u : G) = (u : G) * s := Subgroup.mem_centralizer_iff.mp hu s rfl
      rw [← hcu]
      group
    change Additive.ofMul (Ψ u (⟨s, hsQ⟩ : ↥(Q0sub H)))
      = Additive.ofMul (⟨s, hsQ⟩ : ↥(Q0sub H))
    rw [hval]
  -- (8) the regularity of the `K`-action on `Q₀ \ {0}`
  have hregE : ∀ x y : Additive ↥(Q0sub H), x ≠ 0 → y ≠ 0 →
      ∃! k : ↥(Ksub H t), k • x = y := by
    intro x y hx hy
    have hxne : (Additive.toMul x : ↥(Q0sub H)) ≠ 1 := by
      intro h1
      apply hx
      change Additive.ofMul (Additive.toMul x) = Additive.ofMul (1 : ↥(Q0sub H))
      rw [h1]
    have hyne : (Additive.toMul y : ↥(Q0sub H)) ≠ 1 := by
      intro h1
      apply hy
      change Additive.ofMul (Additive.toMul y) = Additive.ofMul (1 : ↥(Q0sub H))
      rw [h1]
    have hxinv : ((Additive.toMul x : ↥(Q0sub H)) : G) ∈ involutions (H : Set G) :=
      hQ0inv _ (Additive.toMul x).2 (fun h1 => hxne (Subtype.ext h1))
    have hyinv : ((Additive.toMul y : ↥(Q0sub H)) : G) ∈ involutions (H : Set G) :=
      hQ0inv _ (Additive.toMul y).2 (fun h1 => hyne (Subtype.ext h1))
    obtain ⟨k, ⟨hkK, hkx⟩, huniq⟩ := hreg _ hxinv _ hyinv
    have hkKsub : k ∈ Ksub H t := by
      have h' : k ∈ (Ksub H t : Set G) := by rw [hKsub]; exact hkK
      exact h'
    refine ⟨⟨k, hkKsub⟩, ?_, ?_⟩
    · have hval : Φ ⟨k, hkKsub⟩ (Additive.toMul x) = (Additive.toMul y : ↥(Q0sub H)) := by
        apply Subtype.ext
        rw [hΦ]
        exact hkx
      change Additive.ofMul (Φ ⟨k, hkKsub⟩ (Additive.toMul x))
        = Additive.ofMul (Additive.toMul y)
      rw [hval]
    · intro k' hk'
      have hval : ((k' : ↥(Ksub H t)) : G) = k := by
        have hk'' : (Additive.toMul (k' • x) : ↥(Q0sub H)) = (Additive.toMul y : ↥(Q0sub H)) :=
          congrArg Additive.toMul hk'
        have h2 : (Additive.toMul (k' • x) : ↥(Q0sub H)) = Φ k' (Additive.toMul x) := by
          have h3 := smulK_val k' (Additive.toMul x)
          exact congrArg Additive.toMul h3
        rw [h2] at hk''
        have h3 : ((Φ k' (Additive.toMul x) : ↥(Q0sub H)) : G)
            = ((Additive.toMul y : ↥(Q0sub H)) : G) := congrArg Subtype.val hk''
        rw [hΦ] at h3
        have hk'mem : (k' : G) ∈ Kset H t := by
          have h' : (k' : G) ∈ (Ksub H t : Set G) := k'.2
          rwa [hKsub] at h'
        exact huniq (k' : G) ⟨hk'mem, h3⟩
      exact Subtype.ext hval
  -- (9) exponent 2
  have hexp : ∀ x : Additive ↥(Q0sub H), 2 • x = 0 := by
    intro x
    rw [two_nsmul]
    apply Additive.toMul.injective
    change Additive.toMul x * Additive.toMul x = Additive.toMul (0 : Additive ↥(Q0sub H))
    rw [show Additive.toMul (0 : Additive ↥(Q0sub H)) = 1 from rfl]
    exact Subtype.ext (hQ0sq (Additive.toMul x : ↥(Q0sub H)) (Additive.toMul x).2)
  -- (10) apply App. V (a)
  obtain ⟨F, hF, hFt, e₀, κ₀, hes, hκ₀⟩ :=
    appV_regular (p := 2) Nat.prime_two hexp hregE
      (Additive.ofMul (⟨s, hsQ⟩ : ↥(Q0sub H))) hsE0
  letI := hF
  letI := hFt
  -- (11) apply App. V (b),(c)
  obtain ⟨ρ, hρ, hρκ⟩ :=
    appV_semilinear hcompat F e₀ κ₀ (Additive.ofMul (⟨s, hsQ⟩ : ↥(Q0sub H))) hes hκ₀ hUs
  -- (12) packaging
  refine ⟨F, hF, hFt, AddEquiv.toMultiplicative e₀, κ₀, ρ, ?_, ?_, ?_, ?_⟩
  · exact (Nat.card_congr e₀.toEquiv).symm
  · intro k x hx
    have h1 : (⟨(k : G) * x * (k : G)⁻¹, hx⟩ : ↥(Q0sub H)) = Φ k x := by
      apply Subtype.ext
      rw [hΦ]
    rw [h1]
    rw [show (Φ k x : ↥(Q0sub H)) = (k • Additive.ofMul x : Additive ↥(Q0sub H))
        from (smulK_val k x).symm]
    show e₀ (k • Additive.ofMul x) = (κ₀ k : F) * e₀ (Additive.ofMul x)
    exact hκ₀ k (Additive.ofMul x)
  · intro v x hx
    have h1 : (⟨(v : G) * x * (v : G)⁻¹, hx⟩ : ↥(Q0sub H)) = Ψ v x := by
      apply Subtype.ext
      rw [hΨ]
    rw [h1]
    rw [show (Ψ v x : ↥(Q0sub H)) = (v • Additive.ofMul x : Additive ↥(Q0sub H))
        from (smulU_val v x).symm]
    show e₀ (v • Additive.ofMul x) = ρ v (e₀ (Additive.ofMul x))
    exact hρ v (Additive.ofMul x)
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hv
      rw [W, Subgroup.mem_inf]
      refine ⟨v.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hcomm_k : (v : G) * a * (v : G)⁻¹ = a := by
        have h1 : (κ₀ (v • (⟨a, (hKsub_mem a).mpr ha⟩ : ↥(Ksub H t))) : F)
            = (κ₀ (⟨a, (hKsub_mem a).mpr ha⟩ : ↥(Ksub H t)) : F) := by
          rw [hρκ v ⟨a, (hKsub_mem a).mpr ha⟩, hv]
          rfl
        have h2 : v • (⟨a, (hKsub_mem a).mpr ha⟩ : ↥(Ksub H t)) = ⟨a, (hKsub_mem a).mpr ha⟩ :=
          κ₀.injective (Units.ext h1)
        have h3 : (T v ⟨a, (hKsub_mem a).mpr ha⟩ : ↥(Ksub H t)) = ⟨a, (hKsub_mem a).mpr ha⟩ :=
          (smulUK_val v ⟨a, (hKsub_mem a).mpr ha⟩).symm.trans h2
        have h4 := congrArg Subtype.val h3
        rw [hT] at h4
        exact h4
      calc a * (v : G) = ((v : G) * a * (v : G)⁻¹) * (v : G) := by rw [hcomm_k]
        _ = (v : G) * a := by group
    · intro hv
      rw [W, Subgroup.mem_inf] at hv
      have hvcent : ∀ a ∈ Kset H t, a * (v : G) = (v : G) * a :=
        Subgroup.mem_centralizer_iff.mp hv.2
      ext y
      by_cases hy : y = 0
      · rw [hy]; simp
      · obtain ⟨k, hk⟩ := κ₀.surjective (Units.mk0 y hy)
        have hky : (κ₀ k : F) = y := by rw [hk]; exact Units.val_mk0 hy
        have hTk : v • k = k := by
          rw [smulUK_val v k]
          apply Subtype.ext
          rw [hT]
          have hk' : (k : G) ∈ Kset H t := by
            have h' : (k : G) ∈ (Ksub H t : Set G) := k.2
            rwa [hKsub] at h'
          have hc : (k : G) * (v : G) = (v : G) * (k : G) := hvcent (k : G) hk'
          rw [← hc]
          group
        have hfix : ρ v (κ₀ k) = (κ₀ k : F) := by
          rw [← hρκ v k, hTk]
        calc ρ v y = ρ v (κ₀ k : F) := by rw [hky]
          _ = (κ₀ k : F) := hfix
          _ = y := hky
          _ = (1 : F ≃+* F) y := by rfl


end Work.ThmF.ChV12
