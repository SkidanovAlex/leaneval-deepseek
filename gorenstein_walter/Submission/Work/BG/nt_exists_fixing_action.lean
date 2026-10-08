import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.CharBridge
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.S_le_H
import Submission.Work.BG.isFourGroup_closure_pair
import Submission.Work.BG.nCases
import Submission.Work.BG.fixesOrSwapsTwoIrr

/-!
# Area BG: an involutive automorphism of `U` fixing a two-term restriction

In the exceptional configuration (`D.n = 4`, `ξ ∈ Irr(H₀)` `s`-fixed with `ξ|_U = α₁ + α₂`,
`α₁ ≠ α₂`, `|Λξ| = 2`) there is an involutive automorphism `σ` of `U` fixing `α₁` and `α₂`
pointwise, together with a subgroup `L ≤ S` with `[S : L] ≤ 2` centralizing the fixed points
of `σ` in `G`.

The mechanism: `S = ⟨S₀, s⟩ ≤ C_G(t) = H` acts on `U` by conjugation; the restriction
`ξ|_U = α₁ + α₂` is invariant under `conj s` (this is exactly `sconj C ξ = ξ`) and under
`conj (t₁t₂)` (`t₁t₂ ∈ S₀ ≤ H₀`, so `ξ` is class-invariant).  Each of `conj s` and
`conj (t₁t₂)` therefore either fixes `α₁` pointwise or interchanges `α₁` and `α₂`
(`Work.BG.fixesOrSwapsTwoIrr`).  The three cases give `σ = conj s` (with `L = ⟨t, s⟩`),
`σ = conj t₂` (with `L = ⟨t, t₂⟩`, the fixedness of `α₂` being forced by the invariance under
`conj (t₁t₂) = (conj s) (conj t₂)`), or `σ = conj (t₁t₂)` (with `L = S₀`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Conjugation of `U = O_{2'}(H)` by elements of `H` -/

open Work.GW2 Work.GW2.C16 in
/-- `U = O_{2'}(H)` is normal in `H`. -/
theorem nt_U_normal (D : BGData G) : (D.U.subgroupOf D.H).Normal := by
  have h : D.U.subgroupOf D.H = oddCore ↥D.H := by
    rw [show D.U = oddCoreIn D.H from rfl, oddCoreIn, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective D.H.subtype_injective _
  rw [h]
  exact oddCore_normal ↥D.H

open Work.GW2 Work.GW2.C16 in
/-- Conjugation by `g ∈ H` preserves `U`. -/
theorem nt_conj_mem_U {D : BGData G} {C : Sec2Ctx G} (hDC : Compat D C)
    {g u : G} (hg : g ∈ C.P.H) (hu : u ∈ C.P.U) : g * u * g⁻¹ ∈ C.P.U := by
  have hUDH : D.U ≤ D.H := Subgroup.map_subtype_le (oddCore ↥D.H)
  have hg' : g ∈ D.H := by rw [← hDC.H_eq]; exact hg
  have hu' : u ∈ D.U := by rw [← hDC.U_eq]; exact hu
  have hmem := (nt_U_normal D).conj_mem
    (⟨u, hUDH hu'⟩ : ↥D.H) (Subgroup.mem_subgroupOf.mpr hu') (⟨g, hg'⟩ : ↥D.H)
  have h2 : g * u * g⁻¹ ∈ D.U := Subgroup.mem_subgroupOf.mp hmem
  rw [hDC.U_eq]
  exact h2

open Work.GW2 Work.GW2.C16 in
/-- Conjugation by `g ∈ ↥C.P.H` as an automorphism of `↥C.P.U`. -/
noncomputable def nt_conjAutU {D : BGData G} {C : Sec2Ctx G} (hDC : Compat D C)
    (g : ↥C.P.H) : MulAut ↥C.P.U where
  toFun u := ⟨(g : G) * (u : G) * (g : G)⁻¹, nt_conj_mem_U hDC g.2 u.2⟩
  invFun u := ⟨(g : G)⁻¹ * (u : G) * (g : G), by
    have h := nt_conj_mem_U hDC (C.P.H.inv_mem g.2) u.2
    simp only [inv_inv] at h
    exact h⟩
  left_inv u := by
    apply Subtype.ext
    show (g : G)⁻¹ * ((g : G) * (u : G) * (g : G)⁻¹) * (g : G) = (u : G)
    group
  right_inv u := by
    apply Subtype.ext
    show (g : G) * ((g : G)⁻¹ * (u : G) * (g : G)) * (g : G)⁻¹ = (u : G)
    group
  map_mul' u v := by
    apply Subtype.ext
    show (g : G) * ((u : G) * (v : G)) * (g : G)⁻¹
        = ((g : G) * (u : G) * (g : G)⁻¹) * ((g : G) * (v : G) * (g : G)⁻¹)
    group

open Work.GW2 Work.GW2.C16 in
@[simp] theorem nt_conjAutU_apply_coe {D : BGData G} {C : Sec2Ctx G} (hDC : Compat D C)
    (g : ↥C.P.H) (u : ↥C.P.U) :
    (((nt_conjAutU hDC g) u : ↥C.P.U) : G) = (g : G) * (u : G) * (g : G)⁻¹ := rfl

open Work.GW2 Work.GW2.C16 in
theorem nt_conjAutU_mul {D : BGData G} {C : Sec2Ctx G} (hDC : Compat D C)
    (g h : ↥C.P.H) :
    nt_conjAutU hDC (g * h) = nt_conjAutU hDC g * nt_conjAutU hDC h := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  show (g : G) * (h : G) * (u : G) * ((g : G) * (h : G))⁻¹
      = (g : G) * ((h : G) * (u : G) * (h : G)⁻¹) * (g : G)⁻¹
  group

open Work.GW2 Work.GW2.C16 in
theorem nt_conjAutU_one {D : BGData G} {C : Sec2Ctx G} (hDC : Compat D C) :
    nt_conjAutU hDC (1 : ↥C.P.H) = 1 := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  show (1 : G) * (u : G) * (1 : G)⁻¹ = (u : G)
  group

open Work.GW2 Work.GW2.C16 in
/-- Conjugation by elements of `H` is a monoid homomorphism `↥C.P.H →* MulAut ↥C.P.U`. -/
theorem nt_conjHomU (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    ∃ Φ : ↥C.P.H →* MulAut ↥C.P.U, ∀ (g : ↥C.P.H) (u : ↥C.P.U),
      ((Φ g) u : G) = (g : G) * (u : G) * (g : G)⁻¹ :=
  ⟨{ toFun := nt_conjAutU hDC
     map_one' := nt_conjAutU_one hDC
     map_mul' := nt_conjAutU_mul hDC },
    fun _ _ => rfl⟩

/-! ## 2. A tiny closure lemma -/

/-- If `a` and `b` both commute with `u`, then so does every element of `⟨a, b⟩`. -/
theorem nt_closure_comm {u a b : G} (ha : a * u = u * a) (hb : b * u = u * b)
    {l : G} (hl : l ∈ Subgroup.closure ({a, b} : Set G)) : l * u = u * l := by
  have hinv : ∀ x : G, x * u = u * x → x⁻¹ * u = u * x⁻¹ := by
    intro x hx
    calc x⁻¹ * u = x⁻¹ * (u * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * u) * x⁻¹ := by rw [← hx]
      _ = u * x⁻¹ := by group
  exact Subgroup.closure_induction (p := fun l _ => l * u = u * l)
    (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb)
    (by rw [one_mul, mul_one])
    (fun x y _ _ hx hy => by rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc])
    (fun x _ hx => hinv x hx) hl

/-! ## 3. The main theorem -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem nt_exists_fixing_action {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥(C.P.U)] [Invertible (Nat.card ↥(C.P.U) : ℂ)]
    (hDC : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D) (hD4 : D.n = 4)
    {ξ : ClassFunction ↥C.P.H0 ℂ} (hξ : IsIrreducibleCharacter ξ)
    (hξs : Work.BG.sconj C ξ = ξ)
    {α₁ α₂ : ClassFunction ↥(C.P.U) ℂ} (hα₁ : IsIrreducibleCharacter α₁)
    (hα₂ : IsIrreducibleCharacter α₂) (hαne : α₁ ≠ α₂)
    (hξα : restrictU C ξ = α₁ + α₂)
    (hcardξ : (Work.BG.lamOrbit C ξ).ncard = 2) :
    ∃ (σ : MulAut ↥(C.P.U)) (L : Subgroup G),
      σ * σ = 1 ∧ L ≤ (D.S : Subgroup G) ∧ L.relIndex (D.S : Subgroup G) ≤ 2 ∧
      (∀ u : ↥(C.P.U), α₁ (σ u) = α₁ u) ∧ (∀ u : ↥(C.P.U), α₂ (σ u) = α₂ u) ∧
      (∀ u : ↥(C.P.U), σ u = u → ∀ l ∈ L, l * (u : G) = (u : G) * l) := by
  classical
  -- ## membership and cardinality bookkeeping
  have hsH : (D.S : Subgroup G) ≤ D.H := S_le_H D
  have ht1H : D.t1 ∈ C.P.H := by rw [hDC.H_eq]; exact hsH D.t1_mem
  have ht2H : D.t2 ∈ C.P.H := by rw [hDC.H_eq]; exact hsH D.t2_mem
  have hcardS : Nat.card (D.S : Subgroup G) = 2 * D.n := by
    obtain ⟨e⟩ := D.dih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardS8 : Nat.card (D.S : Subgroup G) = 8 := by rw [hcardS, hD4]
  -- ## the conjugation action of `H` on `U`
  obtain ⟨Φ, hΦ⟩ := nt_conjHomU D C hDC
  let g1 : ↥C.P.H := ⟨D.t1, ht1H⟩
  let g2 : ↥C.P.H := ⟨D.t2, ht2H⟩
  let g12 : ↥C.P.H := g1 * g2
  have hg12coe : (g12 : G) = D.t1 * D.t2 := by simp [g12, g1, g2]
  have hτrel : Φ g12 = Φ g1 * Φ g2 := map_mul Φ g1 g2
  -- ## elements of `H₀`
  have ht12H0 : D.t1 * D.t2 ∈ C.P.H0 := by
    rw [hDC.H0_eq]
    show D.t1 * D.t2 ∈ D.U ⊔ D.S0
    exact (le_sup_right : D.S0 ≤ D.U ⊔ D.S0) (by rw [D.gen]; exact Subgroup.mem_zpowers _)
  have hg12mem : (g12 : G) ∈ C.P.H0 := by rw [hg12coe]; exact ht12H0
  -- ## the two involutions `σ = Φ g₁` and `τ = Φ g₁₂`
  have hσ2 : Φ g1 * Φ g1 = 1 := by
    rw [← map_mul]
    have h : g1 * g1 = 1 := by
      apply Subtype.ext
      show D.t1 * D.t1 = 1
      simpa [pow_two, D.t1_order] using pow_orderOf_eq_one D.t1
    rw [h, map_one]
  have hΦ_one_of_central : ∀ g : ↥C.P.H,
      (∀ u : ↥C.P.U, (g : G) * (u : G) = (u : G) * (g : G)) → Φ g = 1 := by
    intro g hg
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hΦ g u]
    show (g : G) * (u : G) * (g : G)⁻¹ = (u : G)
    rw [hg u]
    group
  have hτ2 : Φ g12 * Φ g12 = 1 := by
    rw [← map_mul]
    refine hΦ_one_of_central (g12 * g12) ?_
    intro u
    have hcoe : ((g12 * g12 : ↥C.P.H) : G) = (D.t1 * D.t2) * (D.t1 * D.t2) := by
      rw [Subgroup.coe_mul, hg12coe]
    rw [hcoe]
    have hx : D.t1 * D.t2 ∈ D.S0 := by rw [D.gen]; exact Subgroup.mem_zpowers _
    have hu : (u : G) ∈ D.U := by rw [← hDC.U_eq]; exact u.2
    have h := hS3 (D.t1 * D.t2) hx (u : G) hu
    rwa [pow_two] at h
  -- ## invariance of the restriction `ξ|_U` under `σ = conj s`
  have hres1 : ∀ u : ↥C.P.U, (restrictU C ξ) (Φ g1 u) = (restrictU C ξ) u := by
    intro u
    have hsub : (⟨((Φ g1 u : ↥C.P.U) : G), C.P.U_le_H0 (Φ g1 u).2⟩ : ↥C.P.H0)
        = conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := by
      apply Subtype.ext
      rw [hΦ g1 u, conjMulEquiv_apply]
      show D.t1 * (u : G) * D.t1⁻¹ = (C.s : G) * (u : G) * (C.s : G)⁻¹
      rw [hDC.s_eq]
    have hfix : ξ (conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0))
        = ξ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := by
      have h := congrArg (fun f : ClassFunction ↥C.P.H0 ℂ =>
        f (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)) hξs
      rw [sconj, conjByH_apply] at h
      exact h
    calc (restrictU C ξ) (Φ g1 u)
        = ξ (⟨((Φ g1 u : ↥C.P.U) : G), C.P.U_le_H0 (Φ g1 u).2⟩ : ↥C.P.H0) := rfl
      _ = ξ (conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)) := by rw [hsub]
      _ = ξ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := hfix
      _ = (restrictU C ξ) u := rfl
  have hsum1 : ∀ u : ↥C.P.U, α₁ (Φ g1 u) + α₂ (Φ g1 u) = α₁ u + α₂ u := by
    intro u
    have h := hres1 u
    rw [hξα] at h
    simpa only [ClassFunction.add_apply] using h
  -- ## invariance of the restriction `ξ|_U` under `τ = conj (t₁t₂)`
  have hres12 : ∀ u : ↥C.P.U, (restrictU C ξ) (Φ g12 u) = (restrictU C ξ) u := by
    intro u
    have hsub : (⟨((Φ g12 u : ↥C.P.U) : G), C.P.U_le_H0 (Φ g12 u).2⟩ : ↥C.P.H0)
        = (⟨(g12 : G), hg12mem⟩ : ↥C.P.H0) * (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) *
            (⟨(g12 : G), hg12mem⟩ : ↥C.P.H0)⁻¹ := by
      apply Subtype.ext
      rw [hΦ g12 u]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (restrictU C ξ) (Φ g12 u)
        = ξ (⟨((Φ g12 u : ↥C.P.U) : G), C.P.U_le_H0 (Φ g12 u).2⟩ : ↥C.P.H0) := rfl
      _ = ξ ((⟨(g12 : G), hg12mem⟩ : ↥C.P.H0) * (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) *
            (⟨(g12 : G), hg12mem⟩ : ↥C.P.H0)⁻¹) := by rw [hsub]
      _ = ξ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) :=
          ClassFunction.conj_eq ξ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)
            (⟨(g12 : G), hg12mem⟩ : ↥C.P.H0)
      _ = (restrictU C ξ) u := rfl
  have hsum12 : ∀ u : ↥C.P.U, α₁ (Φ g12 u) + α₂ (Φ g12 u) = α₁ u + α₂ u := by
    intro u
    have h := hres12 u
    rw [hξα] at h
    simpa only [ClassFunction.add_apply] using h
  -- ## each of `σ`, `τ` fixes both `αᵢ` or interchanges them
  have hset1 : (∀ u : ↥C.P.U, α₁ (Φ g1 u) = α₁ u) ∨
      (∀ u : ↥C.P.U, α₁ (Φ g1 u) = α₂ u) := by
    rcases fixesOrSwapsTwoIrr (Φ g1) hα₁ hα₂ hαne hsum1 with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hset12 : (∀ u : ↥C.P.U, α₁ (Φ g12 u) = α₁ u) ∨
      (∀ u : ↥C.P.U, α₁ (Φ g12 u) = α₂ u) := by
    rcases fixesOrSwapsTwoIrr (Φ g12) hα₁ hα₂ hαne hsum12 with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  -- ## the relation `τ u = σ (ρ u)`
  have hτapply : ∀ u : ↥C.P.U, (Φ g12) u = (Φ g1) ((Φ g2) u) := by
    intro u
    rw [hτrel]
    rfl
  rcases hset1 with hA | hB
  · -- ### Case A: `σ = Φ g₁` fixes `α₁`; take `L = ⟨t, s⟩`
    set L : Subgroup G := Subgroup.closure ({(C.t : G), (C.s : G)} : Set G) with hLdef
    have hcardL : Nat.card ↥L = 4 := by
      rw [hLdef]
      exact (isFourGroup_closure_pair (a := (C.t : G)) (b := (C.s : G))
        (by simpa using congrArg (fun x : ↥C.P.H0 => (x : G)) C.t_sq)
        (by simpa using congrArg (fun x : ↥C.P.H => (x : G)) C.s_sq)
        (C.t_comm_H (C.s : G) C.s.2).symm
        (by intro h; exact C.t_not_mem_U (by rw [h]; exact C.P.U.one_mem))
        (by intro h; exact C.s_not_mem_H0 (by rw [h]; exact C.P.H0.one_mem))
        (by intro h; exact C.s_not_mem_H0 (by rw [← h]; exact C.t.2))).1
    have hLle : L ≤ (D.S : Subgroup G) := by
      rw [hLdef, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · rw [hDC.t_eq]; exact D.S0_le D.t_mem
      · rw [hDC.s_eq]; exact D.t1_mem
    have hrel : L.relIndex (D.S : Subgroup G) ≤ 2 := by
      have h := Subgroup.relIndex_mul_card L (D.S : Subgroup G)
      rw [inf_eq_left.mpr hLle, hcardL, hcardS8] at h
      omega
    refine ⟨Φ g1, L, hσ2, hLle, hrel, hA, ?_, ?_⟩
    · intro u
      have hu := hsum1 u
      rw [hA u] at hu
      exact add_left_cancel hu
    · intro u hu l hl
      rw [hLdef] at hl
      have hu' : (C.s : G) * (u : G) * (C.s : G)⁻¹ = (u : G) := by
        have h := congrArg (fun x : ↥C.P.U => (x : G)) hu
        have h' : (D.t1 : G) * (u : G) * (D.t1 : G)⁻¹ = (u : G) := by
          rw [hΦ g1 u] at h
          exact h
        rw [hDC.s_eq]
        exact h'
      have hcomm_s : (C.s : G) * (u : G) = (u : G) * (C.s : G) := by
        calc (C.s : G) * (u : G) = (C.s : G) * (u : G) * (C.s : G)⁻¹ * (C.s : G) := by group
          _ = (u : G) * (C.s : G) := by rw [hu']
      have hcomm_t : (C.t : G) * (u : G) = (u : G) * (C.t : G) :=
        (C.t_comm_H (u : G) (C.P.H0_le_H (C.P.U_le_H0 u.2))).symm
      exact nt_closure_comm hcomm_t hcomm_s hl
  · -- ### Case B: `σ = Φ g₁` interchanges `α₁` and `α₂`
    have hB2 : ∀ u : ↥C.P.U, α₂ (Φ g1 u) = α₁ u := by
      intro u
      have hu := hsum1 u
      rw [hB u, add_comm (α₁ u) (α₂ u)] at hu
      exact add_left_cancel hu
    by_cases hC : ∀ u : ↥C.P.U, α₁ (Φ g2 u) = α₁ u
    · -- ### Case B1: `ρ = Φ g₂` fixes `α₁`; take `L = ⟨t, t₂⟩`
      have hC2 : ∀ u : ↥C.P.U, α₂ (Φ g2 u) = α₂ u := by
        intro u
        have hu := hsum12 u
        have h1 : α₁ (Φ g12 u) = α₂ (Φ g2 u) := by
          rw [hτapply u]; exact hB ((Φ g2) u)
        have h2 : α₂ (Φ g12 u) = α₁ (Φ g2 u) := by
          rw [hτapply u]; exact hB2 ((Φ g2) u)
        rw [h1, h2, hC u] at hu
        rw [add_comm (α₁ u) (α₂ u)] at hu
        exact add_right_cancel hu
      have hρ2 : Φ g2 * Φ g2 = 1 := by
        rw [← map_mul]
        have h : g2 * g2 = 1 := by
          apply Subtype.ext
          show D.t2 * D.t2 = 1
          simpa [pow_two, D.t2_order] using pow_orderOf_eq_one D.t2
        rw [h, map_one]
      set L : Subgroup G := Subgroup.closure ({(D.t : G), D.t2} : Set G) with hLdef
      have hcardL : Nat.card ↥L = 4 := by
        rw [hLdef]
        exact (isFourGroup_closure_pair (a := D.t) (b := D.t2)
          (by rw [← D.t_order]; exact pow_orderOf_eq_one D.t)
          (by rw [← D.t2_order]; exact pow_orderOf_eq_one D.t2)
          ((Subgroup.mem_centralizer_singleton_iff.mp (hsH D.t2_mem)).symm)
          (by intro h
              have h2 := D.t_order
              rw [h, orderOf_one] at h2
              exact absurd h2 (by norm_num))
          (by intro h
              have h2 := D.t2_order
              rw [h, orderOf_one] at h2
              exact absurd h2 (by norm_num))
          (by intro h; exact D.t2_nmem (by rw [← h]; exact D.t_mem))).1
      have hLle : L ≤ (D.S : Subgroup G) := by
        rw [hLdef, Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact D.S0_le D.t_mem
        · exact D.t2_mem
      have hrel : L.relIndex (D.S : Subgroup G) ≤ 2 := by
        have h := Subgroup.relIndex_mul_card L (D.S : Subgroup G)
        rw [inf_eq_left.mpr hLle, hcardL, hcardS8] at h
        omega
      refine ⟨Φ g2, L, hρ2, hLle, hrel, hC, hC2, ?_⟩
      · intro u hu l hl
        rw [hLdef] at hl
        have hu' : D.t2 * (u : G) * D.t2⁻¹ = (u : G) := by
          have h := congrArg (fun x : ↥C.P.U => (x : G)) hu
          rwa [hΦ g2 u] at h
        have hcomm2 : D.t2 * (u : G) = (u : G) * D.t2 := by
          calc D.t2 * (u : G) = D.t2 * (u : G) * D.t2⁻¹ * D.t2 := by group
            _ = (u : G) * D.t2 := by rw [hu']
        have hcommt : D.t * (u : G) = (u : G) * D.t := by
          have h := C.t_comm_H (u : G) (C.P.H0_le_H (C.P.U_le_H0 u.2))
          rw [hDC.t_eq] at h
          exact h.symm
        exact nt_closure_comm hcommt hcomm2 hl
    · -- ### Case B2: neither `σ` nor `ρ` fixes `α₁`; then `τ` does, and `L = S₀`
      have hτfix : ∀ u : ↥C.P.U, α₁ (Φ g12 u) = α₁ u := by
        rcases hset12 with h | h
        · exact h
        · exfalso
          apply hC
          intro u
          have h1 : α₁ (Φ g12 u) = α₂ (Φ g2 u) := by
            rw [hτapply u]; exact hB ((Φ g2) u)
          have h2 : α₂ (Φ g12 u) = α₁ (Φ g2 u) := by
            rw [hτapply u]; exact hB2 ((Φ g2) u)
          have hρu : α₂ (Φ g2 u) = α₂ u := h1.symm.trans (h u)
          have hu := hsum12 u
          rw [h1, h2, hρu] at hu
          rw [add_comm (α₁ u) (α₂ u)] at hu
          exact add_left_cancel hu
      have hτfix2 : ∀ u : ↥C.P.U, α₂ (Φ g12 u) = α₂ u := by
        intro u
        have hu := hsum12 u
        rw [hτfix u] at hu
        exact add_left_cancel hu
      refine ⟨Φ g12, D.S0, hτ2, D.S0_le, ?_, hτfix, hτfix2, ?_⟩
      · exact le_of_eq D.S0_index
      · intro u hu l hl
        have hu' : (D.t1 * D.t2) * (u : G) * (D.t1 * D.t2)⁻¹ = (u : G) := by
          have h := congrArg (fun x : ↥C.P.U => (x : G)) hu
          rw [hΦ g12 u] at h
          rwa [hg12coe] at h
        have hcomm : (D.t1 * D.t2) * (u : G) = (u : G) * (D.t1 * D.t2) := by
          calc (D.t1 * D.t2) * (u : G)
              = (D.t1 * D.t2) * (u : G) * (D.t1 * D.t2)⁻¹ * (D.t1 * D.t2) := by group
            _ = (u : G) * (D.t1 * D.t2) := by rw [hu']
        have hlz : l ∈ Subgroup.zpowers (D.t1 * D.t2) := by rw [← D.gen]; exact hl
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hlz
        rw [← hk]
        exact (Commute.zpow_left hcomm k).eq

end Work.BG
