import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.appX_of_solvable
import Submission.Work.Fitting.Main
import Submission.Work.Fitting.commutator_le_fitting_of_isCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

/-- Conjugation by `τ` as an automorphism of a `τ`-normalised subgroup `H`. -/
noncomputable def jConj {G : Type} [Group G] (H : Subgroup G) (τ : G)
    (h : τ ∈ Subgroup.normalizer (H : Set G)) : MulAut ↥H where
  toFun x := ⟨τ * (x : G) * τ⁻¹, (Subgroup.mem_normalizer_iff.mp h (x : G)).mp x.2⟩
  invFun x := ⟨τ⁻¹ * (x : G) * τ, by
    have h' := (Subgroup.mem_normalizer_iff''.mp h (x : G)).mp x.2
    simpa using h'⟩
  left_inv x := by ext; simp only [Subgroup.coe_mk]; group
  right_inv x := by ext; simp only [Subgroup.coe_mk]; group
  map_mul' x y := by ext; simp only [Subgroup.coe_mul, Subgroup.coe_mk]; group

@[simp] lemma jConj_coe {G : Type} [Group G] (H : Subgroup G) (τ : G)
    (h : τ ∈ Subgroup.normalizer (H : Set G)) (x : ↥H) :
    ((jConj H τ h) x : G) = τ * (x : G) * τ⁻¹ := rfl

/-- The conjugation action of `D` on `A`, for `D ≤ N(A)`. -/
noncomputable def jAct {G : Type} [Group G] (A D : Subgroup G)
    (h : D ≤ Subgroup.normalizer (A : Set G)) : ↥D →* MulAut ↥A where
  toFun d := jConj A (d : G) (h d.2)
  map_one' := by ext x; simp [jConj]
  map_mul' d e := by
    ext x
    simp only [MulAut.mul_apply, jConj_coe, Subgroup.coe_mul]
    group

@[simp] lemma jAct_coe {G : Type} [Group G] (A D : Subgroup G)
    (h : D ≤ Subgroup.normalizer (A : Set G)) (d : ↥D) (x : ↥A) :
    ((jAct A D h d) x : G) = (d : G) * (x : G) * (d : G)⁻¹ := rfl

/-- **`J(D,τ)` is closed under multiplication when `D` is solvable.**

`A` is an elementary abelian `2`-group on which the odd-order group `D` acts faithfully and
transitively on `A ∖ {1}`, `τ` is an involution normalising `D`, and every `x ∈ D` satisfies
`τ x τ⁻¹ · x ∈ [D,D]`.  Then the set of elements of `D` inverted by conjugation by `τ` is closed
under multiplication.

The proof:  by Peterfalvi's Appendix X (`appX_of_solvable`, using solvability and odd order of
`D`) the Fitting subgroup `F(D)` is cyclic and `[D,D] ≤ F(D)`.  Hence `σ := conj_τ` satisfies
`σ x · x ∈ F(D)` for all `x`; moreover conjugation by `σ x` and by `x` agree on the cyclic group
`F(D)` (the automorphism group of a cyclic group is commutative).  Therefore `ψ x` (the
conjugation automorphism of `F(D)` induced by `x`) satisfies `ψ x = ψ x⁻¹`, so `x² ∈ C_D(F(D))`,
and by self-centralisation of the Fitting subgroup in a solvable group `x² ∈ F(D)`.  Thus
`D/F(D)` has exponent `2` and odd order, hence is trivial, i.e. `D = F(D)` is cyclic, in
particular abelian; the claim follows. -/
theorem jformOfSolvable {G : Type} [Group G] (A D : Subgroup G) (τ : G)
    (hA2 : ∀ x ∈ A, x * x = 1) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hDN : D ≤ Subgroup.normalizer (A : Set G)) (hodd : Odd (Nat.card ↥D))
    (hτ2 : τ * τ = 1) (hτN : τ ∈ Subgroup.normalizer (D : Set G))
    [Finite ↥D] [Finite ↥A]
    (htrans : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      ∃! j : G, (j ∈ D ∧ τ * j * τ⁻¹ = j⁻¹) ∧ j * a * j⁻¹ = b)
    (hfaith : D ⊓ Subgroup.centralizer (A : Set G) = ⊥)
    (hgen : ∀ x : ↥D, (⟨τ * (x : G) * τ⁻¹,
        (Subgroup.mem_normalizer_iff.mp hτN (x : G)).mp x.2⟩ : ↥D) * x ∈
        ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆)
    (hDsolv : Group.IsSolvable ↥D) :
    ∀ j₁ ∈ D, τ * j₁ * τ⁻¹ = j₁⁻¹ → ∀ j₂ ∈ D, τ * j₂ * τ⁻¹ = j₂⁻¹ →
      τ * (j₁ * j₂) * τ⁻¹ = (j₁ * j₂)⁻¹ := by
  classical
  -- ## Step 1: `D` acts faithfully and transitively on `A`
  have hfaithρ : Function.Injective (jAct A D hDN) := by
    intro d e hde
    have hmem : ((e⁻¹ * d : ↥D) : G) ∈ D ⊓ Subgroup.centralizer (A : Set G) := by
      refine ⟨(e⁻¹ * d).2, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun a ha => by
        have h := congrArg (fun (f : MulAut ↥A) => ((f ⟨a, ha⟩ : ↥A) : G)) hde
        simp only [jAct_coe] at h
        have h2 : ((e⁻¹ * d : ↥D) : G) * a * ((e⁻¹ * d : ↥D) : G)⁻¹ = a := by
          have hdd : (d : G) * a * (d : G)⁻¹ = (e : G) * a * (e : G)⁻¹ := h
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          calc (e : G)⁻¹ * (d : G) * a * ((e : G)⁻¹ * (d : G))⁻¹
              = (e : G)⁻¹ * ((d : G) * a * (d : G)⁻¹) * (e : G) := by group
            _ = (e : G)⁻¹ * ((e : G) * a * (e : G)⁻¹) * (e : G) := by rw [hdd]
            _ = a := by group
        have hxa : ((e⁻¹ * d : ↥D) : G) * a = a * ((e⁻¹ * d : ↥D) : G) := by
          calc ((e⁻¹ * d : ↥D) : G) * a
              = (((e⁻¹ * d : ↥D) : G) * a * ((e⁻¹ * d : ↥D) : G)⁻¹)
                  * ((e⁻¹ * d : ↥D) : G) := by group
            _ = a * ((e⁻¹ * d : ↥D) : G) := by rw [h2]
        exact hxa.symm)
    rw [hfaith, Subgroup.mem_bot] at hmem
    have h1 : (e⁻¹ * d : ↥D) = 1 := Subtype.ext hmem
    have : e * (e⁻¹ * d) = e * 1 := by rw [h1]
    simpa using this
  have htransρ : ∀ a b : ↥A, a ≠ 1 → b ≠ 1 → ∃ d : ↥D, jAct A D hDN d a = b := by
    intro a b ha hb
    obtain ⟨j, ⟨⟨hjd, _⟩, hja⟩, _⟩ :=
      htrans (a : G) a.2 (fun h => ha (Subtype.ext h)) (b : G) b.2 (fun h => hb (Subtype.ext h))
    exact ⟨⟨j, hjd⟩, by ext; rw [jAct_coe]; exact hja⟩
  -- ## Step 2: Appendix X
  obtain ⟨hFcyc, _hFfpf, hD'F⟩ :=
    Work.PSU3.StageA.appX_of_solvable (D := ↥D) (E := ↥A) hDsolv hodd Nat.prime_two
      (fun x y => Subtype.ext (hAc x.1 x.2 y.1 y.2))
      (fun x => by rw [pow_two]; exact Subtype.ext (hA2 x.1 x.2))
      (jAct A D hDN) hfaithρ htransρ
  -- ## Step 3: setting up `F = F(D)` and `σ = conj_τ`
  let F : Subgroup ↥D := Work.Fitting.fitting ↥D
  haveI hFnormal : F.Normal := Work.Fitting.fitting_normal' ↥D
  haveI hFcycI : IsCyclic ↥F := hFcyc
  haveI hFcomm : IsMulCommutative ↥F := IsCyclic.isMulCommutative
  haveI hAutcomm : IsMulCommutative (MulAut ↥F) :=
    Work.Fitting.isMulCommutative_mulAut_of_isCyclic
  have hD'Fcom : ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ ≤ F :=
    Subgroup.commutator_le.mpr (fun g₁ _ g₂ _ => by
      rw [commutatorElement_def]; exact hD'F g₁ g₂)
  let σ : MulAut ↥D := jConj D τ hτN
  have hσ2 : ∀ x : ↥D, σ (σ x) = x := by
    intro x
    refine Subtype.ext ?_
    change τ * (τ * (x : G) * τ⁻¹) * τ⁻¹ = (x : G)
    rw [show τ * (τ * (x : G) * τ⁻¹) * τ⁻¹ = (τ * τ) * (x : G) * (τ⁻¹ * τ⁻¹) by group]
    rw [hτ2, one_mul, ← mul_inv_rev, hτ2, inv_one, mul_one]
  have hgenF : ∀ x : ↥D, σ x * x ∈ F := by
    intro x
    exact hD'Fcom (show σ x * x ∈ ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ from hgen x)
  -- ## Step 4: `σ` restricted to `F`
  have hFchar : F.Characteristic := Work.Fitting.fitting_characteristic ↥D
  have hσF : ∀ x ∈ F, σ x ∈ F := by
    intro x hx
    have hmap := Subgroup.characteristic_iff_map_eq.mp hFchar σ
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hσFinv : ∀ x ∈ F, σ⁻¹ x ∈ F := by
    intro x hx
    have hmap := Subgroup.characteristic_iff_map_eq.mp hFchar σ⁻¹
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  let T : MulAut ↥F :=
    { toFun := fun x => ⟨σ x.1, hσF x.1 x.2⟩
      invFun := fun x => ⟨σ⁻¹ x.1, hσFinv x.1 x.2⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro x; ext; simp
      map_mul' := by intro x y; ext; simp }
  have hT_coe : ∀ z : ↥F, (T z : ↥D) = σ (z : ↥D) := fun z => rfl
  have hTinv_coe : ∀ z : ↥F, (T⁻¹ z : ↥D) = σ⁻¹ (z : ↥D) := by
    intro z; rw [MulAut.inv_apply]; rfl
  have hθσ : ∀ x : ↥D,
      MulAut.conjNormal (H := F) (σ x) = T * MulAut.conjNormal (H := F) x * T⁻¹ := by
    intro x
    apply MulEquiv.ext
    intro f
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, MulAut.mul_apply, hT_coe, hTinv_coe]
    rw [map_mul, map_mul, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hA : ∀ x : ↥D,
      MulAut.conjNormal (H := F) (σ x) = MulAut.conjNormal (H := F) x := by
    intro x
    rw [hθσ x, mul_comm' T (MulAut.conjNormal (H := F) x), mul_assoc, mul_inv_cancel, mul_one]
  -- ## Step 5: `x * x ∈ F(D)` for all `x`
  have hFker : ∀ y ∈ F, MulAut.conjNormal (H := F) y = 1 := by
    intro y hy
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hcomm : y * (g : ↥D) = (g : ↥D) * y :=
      congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥F) g)
    rw [hcomm]
    group
  have hcen : ∀ y : ↥D, MulAut.conjNormal (H := F) y = 1 →
      y ∈ Subgroup.centralizer (F : Set ↥D) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h := congrArg (fun (φ : MulAut ↥F) => (φ ⟨f, hf⟩ : ↥D)) hy
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc (f : ↥D) * y = (y * (f : ↥D) * y⁻¹) * y := by rw [h]
      _ = y * (f : ↥D) := by group
  have hsq_aut : ∀ x : ↥D,
      MulAut.conjNormal (H := F) x * MulAut.conjNormal (H := F) x = 1 := by
    intro x
    calc MulAut.conjNormal (H := F) x * MulAut.conjNormal (H := F) x
        = MulAut.conjNormal (H := F) (σ x) * MulAut.conjNormal (H := F) x := by rw [hA x]
      _ = MulAut.conjNormal (H := F) (σ x * x) := by rw [map_mul]
      _ = 1 := hFker (σ x * x) (hgenF x)
  have hsq : ∀ x : ↥D, x * x ∈ F := by
    intro x
    have hψ : MulAut.conjNormal (H := F) (x * x) = 1 := by rw [map_mul, hsq_aut x]
    exact Work.Fitting.centralizer_fitting_le ↥D (hcen (x * x) hψ)
  -- ## Step 6: `F = ⊤`
  have hFtop : F = ⊤ := by
    rw [eq_top_iff]
    intro d _
    have hq2 : (QuotientGroup.mk' F d) * (QuotientGroup.mk' F d) = 1 := by
      rw [← map_mul, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (d * d)).mpr (hsq d)
    have hoddq : Odd (Nat.card (↥D ⧸ F)) :=
      Odd.of_dvd_nat hodd ⟨Nat.card ↥F, Subgroup.card_eq_card_quotient_mul_card_subgroup F⟩
    have hone : orderOf (QuotientGroup.mk' F d) = 1 := by
      have h2 : orderOf (QuotientGroup.mk' F d) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hq2)
      have hoddord : Odd (orderOf (QuotientGroup.mk' F d)) :=
        Odd.of_dvd_nat hoddq (orderOf_dvd_natCard _)
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · exact absurd (h ▸ hoddord) (by decide)
    exact (QuotientGroup.eq_one_iff d).mp
      (by simpa [QuotientGroup.mk'_apply] using (orderOf_eq_one_iff.mp hone))
  -- ## Step 7: conclude
  intro j₁ hj₁ hτ₁ j₂ hj₂ hτ₂
  have h1F : (⟨j₁, hj₁⟩ : ↥D) ∈ F := by rw [hFtop]; trivial
  have h2F : (⟨j₂, hj₂⟩ : ↥D) ∈ F := by rw [hFtop]; trivial
  have hcomm : j₁ * j₂ = j₂ * j₁ := by
    have h := mul_comm' (⟨⟨j₁, hj₁⟩, h1F⟩ : ↥F) (⟨⟨j₂, hj₂⟩, h2F⟩ : ↥F)
    simpa using congrArg (fun z : ↥F => (z : G)) h
  have hcomm_inv : j₁⁻¹ * j₂⁻¹ = j₂⁻¹ * j₁⁻¹ := by
    have h := congrArg Inv.inv hcomm
    rw [mul_inv_rev, mul_inv_rev] at h
    exact h.symm
  calc τ * (j₁ * j₂) * τ⁻¹
      = (τ * j₁ * τ⁻¹) * (τ * j₂ * τ⁻¹) := by group
    _ = j₁⁻¹ * j₂⁻¹ := by rw [hτ₁, hτ₂]
    _ = (j₁ * j₂)⁻¹ := by rw [mul_inv_rev, hcomm_inv]

end Work.ThmF.ChV12
