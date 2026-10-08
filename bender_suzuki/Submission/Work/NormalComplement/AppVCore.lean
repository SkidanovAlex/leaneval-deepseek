/-
# The abstract core of Peterfalvi Appendix V (d)
-/
import Mathlib
import Submission.Work.NormalComplement.AppVDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Polynomial Module

namespace Work.NormalComplement

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

/-! ## A. The universal property of `k[X]/(minpoly k φ)` -/

/-- The identity map, viewed as a ring hom between the two presentations of the same quotient. -/
private noncomputable def adjoinRootToQuotient {K : Type*} [CommRing K] (f : Polynomial K) :
    AdjoinRoot f →+* (Polynomial K ⧸ Ideal.span {f}) where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The universal property of `k[X]/(minpoly k φ)`**: polynomial evaluation at `φ` descends to the
quotient by the minimal polynomial. -/
private lemma exists_quotient_endHom (φ : V →ₗ[k] V) :
    ∃ ρ : AdjoinRoot (minpoly k φ) →+* Module.End k V,
      ρ (AdjoinRoot.root (minpoly k φ)) = φ ∧
      (∀ Q : Polynomial k, ρ (AdjoinRoot.mk (minpoly k φ) Q) = Polynomial.aeval φ Q) := by
  have hker : ∀ a ∈ Ideal.span {minpoly k φ}, (Polynomial.aeval φ) a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, minpoly.aeval, zero_mul]
  refine ⟨(Ideal.Quotient.lift (Ideal.span {minpoly k φ}) (Polynomial.aeval φ).toRingHom hker).comp
    (adjoinRootToQuotient (minpoly k φ)), ?_, ?_⟩
  · have h1 : adjoinRootToQuotient (minpoly k φ) (AdjoinRoot.root (minpoly k φ))
        = Ideal.Quotient.mk _ (Polynomial.X) := rfl
    rw [RingHom.comp_apply, h1, Ideal.Quotient.lift_mk]
    exact Polynomial.aeval_X φ
  · intro Q
    rw [RingHom.comp_apply]
    show (Ideal.Quotient.lift (Ideal.span {minpoly k φ}) (Polynomial.aeval φ).toRingHom hker)
      (Ideal.Quotient.mk _ Q) = Polynomial.aeval φ Q
    exact Ideal.Quotient.lift_mk _ _ hker

/-- Conjugation by a linear equivalence commutes with polynomial evaluation. -/
private lemma aeval_conj (e : V ≃ₗ[k] V) (s : V →ₗ[k] V) (p : Polynomial k) :
    Polynomial.aeval ((e : V →ₗ[k] V) * s * (e.symm : V →ₗ[k] V)) p =
      (e : V →ₗ[k] V) * Polynomial.aeval s p * (e.symm : V →ₗ[k] V) := by
  have h := Polynomial.aeval_algHom_apply (e.conjAlgEquiv k) s p
  simp only [LinearEquiv.conjAlgEquiv_apply] at h
  exact h

/-- The coercion `V ≃ₗ[k] V → V →ₗ[k] V` preserves powers. -/
private lemma coe_pow_eq (t : V ≃ₗ[k] V) (n : ℕ) :
    ((t ^ n : V ≃ₗ[k] V) : V →ₗ[k] V) = (t : V →ₗ[k] V) ^ n := by
  induction n with
  | zero => exact Module.End.one_eq_id.symm
  | succ n ih => simp [pow_succ, ih]

/-- Conjugating a power. -/
private lemma conj_pow_eq (a s : V ≃ₗ[k] V) (m : ℕ) :
    (a * s * a⁻¹) ^ m = a * s ^ m * a⁻¹ := by
  rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]

/-! ## B. The minimal polynomial of an irreducible automorphism is irreducible -/

/-- If `t` has no non-trivial invariant subspace (and `V ≠ 0`), then `minpoly k t` is irreducible. -/
private lemma irreducible_minpoly (t : V ≃ₗ[k] V) [Nontrivial V] [Finite V]
    (hirr : ∀ W : Submodule k V, (∀ x ∈ W, t x ∈ W) → W = ⊥ ∨ W = ⊤) :
    Irreducible (minpoly k (t : V →ₗ[k] V)) := by
  classical
  haveI : Module.Finite k V := Module.Finite.of_finite
  haveI : Module.Free k V := Module.Free.of_divisionRing k V
  set s : V →ₗ[k] V := ((t : V ≃ₗ[k] V) : V →ₗ[k] V) with hs
  set g : Polynomial k := minpoly k s with hg
  have haev : Polynomial.aeval s g = 0 := by rw [hg]; exact minpoly.aeval k s
  have hsX : s = Polynomial.aeval s (Polynomial.X : Polynomial k) :=
    (Polynomial.aeval_X (R := k) s).symm
  have hcomm : ∀ p : Polynomial k, Polynomial.aeval s p * s = s * Polynomial.aeval s p := by
    intro p
    have key := congrArg (Polynomial.aeval s) (mul_comm p (Polynomial.X : Polynomial k))
    simp only [map_mul, Polynomial.aeval_X] at key
    exact key
  have hst : ∀ x : V, s x = t x := fun _ => rfl
  have hgne0 : g ≠ 0 := minpoly.ne_zero (LinearMap.isIntegral s)
  refine ⟨?_, ?_⟩
  · -- `g` is not a unit
    intro hunit
    have hdeg0 : g.degree = 0 := Polynomial.degree_eq_zero_of_isUnit hunit
    have hC : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_degree_eq_zero hdeg0
    have hne : g.coeff 0 ≠ 0 := fun h0 => hgne0 (by rw [hC, h0, Polynomial.C_0])
    rw [hC, Polynomial.aeval_C] at haev
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 : g.coeff 0 • v = 0 := by
      have h3 := congr_fun (congr_arg DFunLike.coe haev) v
      simpa using h3
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact hne h3
    · exact hv h3
  · intro a b hab
    by_cases ha : a = 0
    · rw [ha, zero_mul] at hab; exact absurd hab hgne0
    by_cases hb : b = 0
    · rw [hb, mul_zero] at hab; exact absurd hab hgne0
    have hdeg : g.natDegree = a.natDegree + b.natDegree := by
      rw [hab, Polynomial.natDegree_mul ha hb]
    by_cases hda : a.natDegree = 0
    · left
      have hC : a = Polynomial.C (a.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hda
      rw [hC, Polynomial.isUnit_C, isUnit_iff_ne_zero]
      intro h0
      exact ha (by rw [hC, h0, Polynomial.C_0])
    by_cases hdb : b.natDegree = 0
    · right
      have hC : b = Polynomial.C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdb
      rw [hC, Polynomial.isUnit_C, isUnit_iff_ne_zero]
      intro h0
      exact hb (by rw [hC, h0, Polynomial.C_0])
    have hda1 : 1 ≤ a.natDegree := Nat.one_le_iff_ne_zero.mpr hda
    have hdb1 : 1 ≤ b.natDegree := Nat.one_le_iff_ne_zero.mpr hdb
    have hanev : Polynomial.aeval s a ≠ 0 := by
      intro h0
      have hdvd : g ∣ a := by rw [hg]; exact minpoly.dvd k s h0
      have := Polynomial.natDegree_le_of_dvd hdvd ha
      omega
    have hbnev : Polynomial.aeval s b ≠ 0 := by
      intro h0
      have hdvd : g ∣ b := by rw [hg]; exact minpoly.dvd k s h0
      have := Polynomial.natDegree_le_of_dvd hdvd hb
      omega
    have hmul : Polynomial.aeval s b * Polynomial.aeval s a = 0 := by
      rw [← map_mul, mul_comm, ← hab, haev]
    have hnotinj : ¬ Function.Injective (Polynomial.aeval s a : V →ₗ[k] V) := by
      intro hinj
      have hsurj := LinearMap.surjective_of_injective hinj
      have hzero : Polynomial.aeval s b = 0 := by
        refine LinearMap.ext fun x => ?_
        obtain ⟨y, rfl⟩ := hsurj x
        have h1 : (Polynomial.aeval s b * Polynomial.aeval s a) y = 0 := by rw [hmul]; rfl
        simpa using h1
      exact hbnev hzero
    have hker_bot : LinearMap.ker (Polynomial.aeval s a : V →ₗ[k] V) ≠ ⊥ := by
      intro h
      exact hnotinj (LinearMap.ker_eq_bot.mp h)
    have hker_top : LinearMap.ker (Polynomial.aeval s a : V →ₗ[k] V) ≠ ⊤ := by
      intro h
      apply hanev
      refine LinearMap.ext fun x => ?_
      have hx : x ∈ LinearMap.ker (Polynomial.aeval s a : V →ₗ[k] V) := by
        rw [h]; exact Submodule.mem_top
      simpa using hx
    have hinv : ∀ x ∈ LinearMap.ker (Polynomial.aeval s a : V →ₗ[k] V),
        t x ∈ LinearMap.ker (Polynomial.aeval s a : V →ₗ[k] V) := by
      intro x hx
      have hx' : Polynomial.aeval s a x = 0 := hx
      have h1 : Polynomial.aeval s a (s x) = s (Polynomial.aeval s a x) := by
        have := congr_fun (congr_arg DFunLike.coe (hcomm a)) x
        simpa using this
      show Polynomial.aeval s a (t x) = 0
      rw [← hst x, h1, hx', map_zero]
    rcases hirr _ hinv with h | h
    · exact absurd h hker_bot
    · exact absurd h hker_top


/-! ## C. The main argument -/

/-- **Peterfalvi I App. V (d), abstract core.** -/
theorem appVCoreProp : AppVCoreProp := by
  unfold AppVCoreProp
  intro k V _ _ _ _ _ t hirr U htU hnorm P hPU hPne hfix
  classical
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype V := Fintype.ofFinite V
  -- (0) `V` is non-trivial
  have hk2 : 2 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hfixP : Nat.card {v : V // ∀ u ∈ P, u v = v} = Nat.card k := hfix P le_rfl hPne
  have hV2 : 2 ≤ Nat.card V := by
    have hle : Nat.card {v : V // ∀ u ∈ P, u v = v} ≤ Nat.card V :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    omega
  haveI : Nontrivial V := by
    rw [Nat.card_eq_fintype_card] at hV2
    exact Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI : Module.Finite k V := Module.Finite.of_finite
  haveI : Module.Free k V := Module.Free.of_divisionRing k V
  haveI : Finite (V ≃ₗ[k] V) :=
    Finite.of_injective (fun e : V ≃ₗ[k] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (fun x => congr_fun h x))
  -- (1) the field `F = k[X]/(minpoly k t)`
  set tE : V →ₗ[k] V := ((t : V ≃ₗ[k] V) : V →ₗ[k] V) with htE
  set g : Polynomial k := minpoly k tE with hg
  have hgmonic : g.Monic := hg ▸ minpoly.monic (LinearMap.isIntegral tE)
  have hgne : g ≠ 0 := hgmonic.ne_zero
  have haev : Polynomial.aeval tE g = 0 := hg ▸ minpoly.aeval k tE
  have hgirr : Irreducible g := by rw [hg]; exact irreducible_minpoly t hirr
  haveI : Fact (Irreducible g) := ⟨hgirr⟩
  obtain ⟨φ, hφroot, hφmk⟩ := exists_quotient_endHom tE
  have hφC : ∀ c : k, φ (algebraMap k (AdjoinRoot g) c) = algebraMap k (V →ₗ[k] V) c := by
    intro c
    have h1 : algebraMap k (AdjoinRoot g) c = AdjoinRoot.mk g (Polynomial.C c) := by
      rw [AdjoinRoot.algebraMap_eq]; rfl
    rw [h1, hφmk, Polynomial.aeval_C]
  have hφsmul : ∀ (c : k) (x : AdjoinRoot g), φ (c • x) = c • φ x := by
    intro c x
    rw [Algebra.smul_def, map_mul, hφC, ← Algebra.smul_def]
  let φa : AdjoinRoot g →ₐ[k] (V →ₗ[k] V) := AlgHom.mk' φ hφsmul
  have hφa_eq : φa = AlgHom.mk' φ hφsmul := rfl
  have hφa_root : φa (AdjoinRoot.root g) = tE := hφroot
  have hφa_mk : ∀ Q : Polynomial k, φa (AdjoinRoot.mk g Q) = Polynomial.aeval tE Q := hφmk
  have hφinj : Function.Injective φa := by
    intro x y hxy
    by_contra hne
    obtain ⟨w, hw⟩ := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne : x - y ≠ 0)
    have h0 : φa (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : φa ((x - y) * ↑w⁻¹) = 1 := by rw [← hw, Units.mul_inv, map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  -- (2) elementary cardinalities for `F`
  have hFinF : Module.finrank k (AdjoinRoot g) = g.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hgne), AdjoinRoot.powerBasis_dim hgne]
  haveI : Module.Finite k (AdjoinRoot g) := Module.Finite.of_basis (AdjoinRoot.powerBasis hgne).basis
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite k
  have hcardF : Nat.card (AdjoinRoot g) = Nat.card k ^ g.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := k) (V := AdjoinRoot g), hFinF]
  -- (3) the bijection `λ ↦ φa λ v` for `v ≠ 0`
  have hrange_top : ∀ v : V, v ≠ 0 → ∀ x : V, ∃ μ : AdjoinRoot g, φa μ v = x := by
    intro v hv x
    let W : Submodule k V :=
      { carrier := Set.range (fun m : AdjoinRoot g => φa m v)
        zero_mem' := ⟨0, by simp⟩
        add_mem' := by
          rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
          exact ⟨m + n, by simp [map_add]⟩
        smul_mem' := by
          rintro c a ⟨m, rfl⟩
          exact ⟨c • m, by simp [hφsmul]⟩ }
    have hWne : W ≠ ⊥ := by
      intro h
      have hvW : v ∈ W := ⟨1, by simp⟩
      rw [h] at hvW
      exact hv (by simpa using hvW)
    have hWinv : ∀ y ∈ W, t y ∈ W := by
      rintro y ⟨m, rfl⟩
      refine ⟨AdjoinRoot.root g * m, ?_⟩
      show φa (AdjoinRoot.root g * m) v = t (φa m v)
      rw [map_mul, hφa_root]
      rfl
    rcases hirr W hWinv with h | h
    · exact absurd h hWne
    · obtain ⟨m, hm⟩ := (show x ∈ W from by rw [h]; exact Submodule.mem_top)
      exact ⟨m, hm⟩
  have hbij : ∀ v : V, v ≠ 0 → Function.Bijective (fun m : AdjoinRoot g => φa m v) := by
    intro v hv
    refine ⟨?_, hrange_top v hv⟩
    intro m n hmn
    by_contra hne
    obtain ⟨w, hw⟩ := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne : m - n ≠ 0)
    have h0 : φa (m - n) v = 0 := by
      rw [map_sub, show (φa m - φa n) v = φa m v - φa n v from rfl, sub_eq_zero]
      exact hmn
    have hleft : φa (↑w⁻¹) * φa (m - n) = 1 := by
      rw [← map_mul, ← hw, Units.inv_mul, map_one]
    have hfin : v = 0 := by
      calc v = (φa (↑w⁻¹) * φa (m - n)) v := by rw [hleft]; rfl
        _ = φa (↑w⁻¹) (φa (m - n) v) := rfl
        _ = φa (↑w⁻¹) 0 := by rw [h0]
        _ = 0 := map_zero _
    exact hv hfin
  -- (4) `natDegree g = dim V`, so `|F| = |k| ^ n`
  have hdeg_eq : g.natDegree = Module.finrank k V := by
    obtain ⟨v0, hv0⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
    have hcard : Nat.card (AdjoinRoot g) = Nat.card V :=
      Nat.card_congr (Equiv.ofBijective _ (hbij v0 hv0))
    rw [hcardF, Module.natCard_eq_pow_finrank (K := k) (V := V)] at hcard
    exact Nat.pow_right_injective hk2 hcard
  have hgal_card : Nat.card (AdjoinRoot g ≃ₐ[k] AdjoinRoot g) = Module.finrank k V := by
    rw [IsGalois.card_aut_eq_finrank k, hFinF, hdeg_eq]
  have hgalois : ∀ H : Subgroup (AdjoinRoot g ≃ₐ[k] AdjoinRoot g),
      Nat.card (IntermediateField.fixedField H) =
        Nat.card k ^ (Module.finrank k V / Nat.card H) := by
    intro H
    have h1 : Module.finrank k (IntermediateField.fixedField H) * Nat.card H
        = Module.finrank k V := by
      rw [← IntermediateField.finrank_fixedField_eq_card (F := k) (E := AdjoinRoot g) H]
      rw [Module.finrank_mul_finrank k (IntermediateField.fixedField H) (AdjoinRoot g)]
      rw [hFinF, hdeg_eq]
    have h2 : Module.finrank k (IntermediateField.fixedField H)
        = Module.finrank k V / Nat.card H :=
      Nat.eq_div_of_mul_eq_right (Nat.card_pos.ne') (by rw [mul_comm]; exact h1)
    rw [← h2]
    exact Module.natCard_eq_pow_finrank (K := k) (V := IntermediateField.fixedField H)
  -- (5) the semilinear structure
  have hnorm_nat : ∀ u : V ≃ₗ[k] V, u ∈ U → ∃ n : ℕ, t ^ n = u * t * u⁻¹ := by
    intro u hu
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hnorm u hu)
    refine ⟨(m % (orderOf t : ℤ)).toNat, ?_⟩
    have hmpos : (0 : ℤ) < (orderOf t : ℤ) := by
      exact_mod_cast orderOf_pos t
    have hnn : 0 ≤ m % (orderOf t : ℤ) := Int.emod_nonneg m hmpos.ne'
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_mod_orderOf]
    exact hm
  choose nu hnu using hnorm_nat
  have hroot_mem : ∀ (u : V ≃ₗ[k] V) (hu : u ∈ U),
      Polynomial.aeval (AdjoinRoot.root g ^ nu u hu) g = 0 := by
    intro u hu
    apply hφinj
    rw [← Polynomial.aeval_algHom_apply φa, map_zero]
    have h1 : φa (AdjoinRoot.root g ^ nu u hu) = tE ^ nu u hu := by
      rw [map_pow, hφa_root]
    rw [h1, ← coe_pow_eq t (nu u hu), hnu u hu]
    rw [show ((u * t * u⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V)
        = (u : V →ₗ[k] V) * tE * (u.symm : V →ₗ[k] V) from rfl]
    rw [aeval_conj, haev]
    simp
  have hσ_hom : ∀ (u : V ≃ₗ[k] V) (hu : u ∈ U), ∃ σ : AdjoinRoot g →+* AdjoinRoot g,
      σ (AdjoinRoot.root g) = AdjoinRoot.root g ^ nu u hu ∧
      (∀ Q : Polynomial k,
        σ (AdjoinRoot.mk g Q) = Polynomial.aeval (AdjoinRoot.root g ^ nu u hu) Q) := by
    intro u hu
    have hker : ∀ a ∈ Ideal.span {g},
        (Polynomial.aeval (AdjoinRoot.root g ^ nu u hu)) a = 0 := by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [map_mul, hroot_mem u hu, zero_mul]
    refine ⟨(Ideal.Quotient.lift (Ideal.span {g})
      (Polynomial.aeval (AdjoinRoot.root g ^ nu u hu)).toRingHom hker).comp
      (adjoinRootToQuotient g), ?_, ?_⟩
    · have h1 : adjoinRootToQuotient g (AdjoinRoot.root g)
          = Ideal.Quotient.mk _ (Polynomial.X) := rfl
      rw [RingHom.comp_apply, h1, Ideal.Quotient.lift_mk]
      exact Polynomial.aeval_X _
    · intro Q
      rw [RingHom.comp_apply]
      show (Ideal.Quotient.lift (Ideal.span {g})
        (Polynomial.aeval (AdjoinRoot.root g ^ nu u hu)).toRingHom hker)
        (Ideal.Quotient.mk _ Q) = _
      exact Ideal.Quotient.lift_mk _ _ hker
  choose σr hσr_root hσr_mk using hσ_hom
  have hσr_smul : ∀ (u : V ≃ₗ[k] V) (hu : u ∈ U) (c : k) (x : AdjoinRoot g),
      σr u hu (c • x) = c • σr u hu x := by
    intro u hu c x
    induction x using AdjoinRoot.induction_on with
    | _ Q =>
      rw [AdjoinRoot.smul_mk, Polynomial.smul_eq_C_mul,
        hσr_mk u hu (Polynomial.C c * Q), hσr_mk u hu Q, map_mul, Polynomial.aeval_C,
        ← Algebra.smul_def]
  let σa : (u : V ≃ₗ[k] V) → u ∈ U → AdjoinRoot g →ₐ[k] AdjoinRoot g :=
    fun u hu => AlgHom.mk' (σr u hu) (hσr_smul u hu)
  have hσ_root : ∀ (u : V ≃ₗ[k] V) (hu : u ∈ U),
      σa u hu (AdjoinRoot.root g) = AdjoinRoot.root g ^ nu u hu := by
    intro u hu
    show σr u hu (AdjoinRoot.root g) = AdjoinRoot.root g ^ nu u hu
    rw [hσr_root u hu]
  have hσ_mk : ∀ (u : V ≃ₗ[k] V) (hu : u ∈ U) (Q : Polynomial k),
      σa u hu (AdjoinRoot.mk g Q)
        = Polynomial.aeval (AdjoinRoot.root g ^ nu u hu) Q := by
    intro u hu Q
    show σr u hu (AdjoinRoot.mk g Q) = _
    rw [hσr_mk u hu Q]
  have hσ_op : ∀ (u : V ≃ₗ[k] V) (hu : u ∈ U) (m : AdjoinRoot g),
      φa (σa u hu m) = (u : V →ₗ[k] V) * φa m * (u.symm : V →ₗ[k] V) := by
    intro u hu m
    induction m using AdjoinRoot.induction_on with
    | _ Q =>
      rw [hσ_mk u hu Q, ← Polynomial.aeval_algHom_apply φa]
      have h1 : φa (AdjoinRoot.root g ^ nu u hu) = tE ^ nu u hu := by
        rw [map_pow, hφa_root]
      rw [h1, ← coe_pow_eq t (nu u hu), hnu u hu]
      rw [show ((u * t * u⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V)
          = (u : V →ₗ[k] V) * tE * (u.symm : V →ₗ[k] V) from rfl]
      rw [aeval_conj, hφa_mk]
  have hσ_apply : ∀ (u : V ≃ₗ[k] V) (hu : u ∈ U) (m : AdjoinRoot g) (x : V),
      u (φa m x) = φa (σa u hu m) (u x) := by
    intro u hu m x
    have h1 : φa (σa u hu m) (u x) = u (φa m x) := by
      have h2 := congr_fun (congr_arg DFunLike.coe (hσ_op u hu m)) (u x)
      rw [h2]
      show ((u : V →ₗ[k] V) * φa m * (u.symm : V →ₗ[k] V)) (u x) = u (φa m x)
      rw [show ((u : V →ₗ[k] V) * φa m * (u.symm : V →ₗ[k] V)) (u x)
          = u (φa m (u.symm (u x))) from rfl, LinearEquiv.symm_apply_apply]
    exact h1.symm
  have hσ_mul : ∀ (u v : V ≃ₗ[k] V) (hu : u ∈ U) (hv : v ∈ U),
      σa (u * v) (U.mul_mem hu hv) = (σa u hu).comp (σa v hv) := by
    intro u v hu hv
    have hgroup : t ^ nu (u * v) (U.mul_mem hu hv) = (t ^ nu u hu) ^ nu v hv := by
      rw [hnu (u * v) (U.mul_mem hu hv), hnu u hu, conj_pow_eq, hnu v hv]
      group
    apply AdjoinRoot.algHom_ext
    rw [hσ_root (u * v) (U.mul_mem hu hv), AlgHom.comp_apply, hσ_root v hv, map_pow,
      hσ_root u hu]
    apply hφinj
    rw [map_pow, map_pow, map_pow, hφa_root, ← coe_pow_eq t (nu (u * v) (U.mul_mem hu hv)),
      ← coe_pow_eq t (nu u hu), ← coe_pow_eq (t ^ nu u hu) (nu v hv), hgroup]
  have hσ_one : σa 1 U.one_mem = AlgHom.id k (AdjoinRoot g) := by
    have h1 : t ^ nu 1 U.one_mem = t := by rw [hnu 1 U.one_mem]; simp
    have h2 : AdjoinRoot.root g ^ nu 1 U.one_mem = AdjoinRoot.root g := by
      apply hφinj
      rw [map_pow, hφa_root, ← coe_pow_eq t (nu 1 U.one_mem), h1]
    apply AdjoinRoot.algHom_ext
    rw [hσ_root 1 U.one_mem, h2, AlgHom.id_apply]
  have hσ_bij : ∀ (u : V ≃ₗ[k] V) (hu : u ∈ U), Function.Bijective (σa u hu) := by
    intro u hu
    have hinj : Function.Injective (σa u hu) := by
      intro a b hab
      by_contra hne
      obtain ⟨w, hw⟩ := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne : a - b ≠ 0)
      have h0 : σa u hu (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have h1 : σa u hu ((a - b) * ↑w⁻¹) = 1 := by rw [← hw, Units.mul_inv, map_one]
      rw [map_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩
  let σhom : U →* (AdjoinRoot g ≃ₐ[k] AdjoinRoot g) :=
    { toFun := fun u => AlgEquiv.ofBijective (σa u u.2) (hσ_bij u u.2)
      map_one' := by
        apply AlgEquiv.ext
        intro m
        show σa 1 U.one_mem m = m
        rw [hσ_one]; rfl
      map_mul' := fun u v => by
        apply AlgEquiv.ext
        intro m
        show σa (u * v) (U.mul_mem u.2 v.2) m = σa u u.2 (σa v v.2 m)
        rw [hσ_mul u v u.2 v.2]; rfl }
  have hσhom_val : ∀ (u : V ≃ₗ[k] V) (hu : u ∈ U),
      σhom ⟨u, hu⟩ = AlgEquiv.ofBijective (σa u hu) (hσ_bij u hu) := fun _ _ => rfl
  -- (6) the fixed space of `P₁` is the fixed field of `σP(P₁)`
  have hP1_card : ∀ P₁ : Subgroup (V ≃ₗ[k] V), P₁ ≤ P → P₁ ≠ ⊥ →
      Nat.card P₁ = Module.finrank k V := by
    intro P₁ hP₁ hP₁ne
    -- a non-zero vector fixed by `P₁`
    have hfix1 : Nat.card {v : V // ∀ u ∈ P₁, u v = v} = Nat.card k := hfix P₁ hP₁ hP₁ne
    have hc2 : 2 ≤ Nat.card {v : V // ∀ u ∈ P₁, u v = v} := by rw [hfix1]; omega
    haveI : Fintype {v : V // ∀ u ∈ P₁, u v = v} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hc2
    haveI : Nontrivial {v : V // ∀ u ∈ P₁, u v = v} :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a0, b0, hab0⟩ := exists_pair_ne {v : V // ∀ u ∈ P₁, u v = v}
    obtain ⟨s, hsfix, hsne⟩ : ∃ s : V, (∀ u ∈ P₁, u s = s) ∧ s ≠ 0 := by
      rcases eq_or_ne a0.1 0 with h | h
      · exact ⟨b0.1, b0.2, fun hb => hab0 (Subtype.ext (by rw [h, hb]))⟩
      · exact ⟨a0.1, a0.2, h⟩
    -- the group hom `P₁ → Gal(F/k)`
    let σP : P₁ →* (AdjoinRoot g ≃ₐ[k] AdjoinRoot g) :=
      σhom.comp (Subgroup.inclusion (le_trans hP₁ hPU) : P₁ →* U)
    have hσP_apply : ∀ u : P₁, σP u = σhom ⟨u.1, hPU (hP₁ u.2)⟩ := fun u => rfl
    have hσP_val : ∀ (u : P₁) (m : AdjoinRoot g), σP u m = σa u.1 (hPU (hP₁ u.2)) m :=
      fun _ _ => rfl
    have hinj : Function.Injective σP := by
      intro a b hab
      have key : ∀ m : AdjoinRoot g, (a : V ≃ₗ[k] V) (φa m s) = (b : V ≃ₗ[k] V) (φa m s) := by
        intro m
        have ha' := hσ_apply (a : V ≃ₗ[k] V) (hPU (hP₁ a.2)) m s
        have hb' := hσ_apply (b : V ≃ₗ[k] V) (hPU (hP₁ b.2)) m s
        rw [hsfix (a : V ≃ₗ[k] V) a.2] at ha'
        rw [hsfix (b : V ≃ₗ[k] V) b.2] at hb'
        rw [ha', hb']
        have hab' : σa (a : V ≃ₗ[k] V) (hPU (hP₁ a.2)) m
            = σa (b : V ≃ₗ[k] V) (hPU (hP₁ b.2)) m := DFunLike.congr_fun hab m
        exact congrArg (fun z => φa z s) hab'
      refine Subtype.ext (LinearEquiv.ext fun x => ?_)
      obtain ⟨m, rfl⟩ := (hbij s hsne).2 x
      exact key m
    set H : Subgroup (AdjoinRoot g ≃ₐ[k] AdjoinRoot g) := σP.range with hH
    have hcardP1 : Nat.card H = Nat.card P₁ := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun u : P₁ => (⟨σP u, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩ : H)) ⟨?_, ?_⟩).symm
      · intro a b hab
        exact hinj (Subtype.ext_iff.mp hab)
      · rintro ⟨f, hf⟩
        obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hf
        exact ⟨u, rfl⟩
    -- the fixed field of `H`
    have hfixfield : Nat.card (IntermediateField.fixedField H) = Nat.card k := by
      have e1 : {m : AdjoinRoot g // ∀ u : P₁, σP u m = m} ≃
          IntermediateField.fixedField H :=
        Equiv.subtypeEquivRight (fun m => by
          rw [IntermediateField.mem_fixedField_iff (H := H)]
          constructor
          · intro hm f hf
            rw [hH] at hf
            obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hf
            exact hm u
          · intro hm u
            exact hm (σP u) (MonoidHom.mem_range.mpr ⟨u, rfl⟩))
      have e2 : {m : AdjoinRoot g // ∀ u : P₁, σP u m = m} ≃
          {v : V // ∀ u ∈ P₁, u v = v} :=
        Equiv.subtypeEquiv (Equiv.ofBijective (fun m : AdjoinRoot g => φa m s) (hbij s hsne))
          (fun m => by
            constructor
            · intro hm u hu
              have h1 := hσ_apply u (hPU (hP₁ hu)) m s
              rw [hsfix u hu, ← hσP_val ⟨u, hu⟩ m, hm ⟨u, hu⟩] at h1
              exact h1
            · intro hv u
              have h2 : φa (σa u.1 (hPU (hP₁ u.2)) m) s = φa m s := by
                have h1 := hσ_apply u.1 (hPU (hP₁ u.2)) m s
                rw [hsfix u.1 u.2] at h1
                rw [← h1]
                exact hv u.1 u.2
              have h3 : σa u.1 (hPU (hP₁ u.2)) m = m := (hbij s hsne).1 h2
              rw [hσP_val u m]
              exact h3)
      rw [← hfix1]
      exact Nat.card_congr (e1.symm.trans e2)
    have hHcard : Nat.card H = Module.finrank k V := by
      have h1 : Nat.card (IntermediateField.fixedField H)
          = Nat.card k ^ (Module.finrank k V / Nat.card H) := hgalois H
      rw [hfixfield] at h1
      have h2 : Nat.card k ^ (Module.finrank k V / Nat.card H) = Nat.card k ^ 1 := by
        rw [← h1, pow_one]
      have h3 : Module.finrank k V / Nat.card H = 1 := Nat.pow_right_injective hk2 h2
      have h4 : Module.finrank k (IntermediateField.fixedField H) * Nat.card H
          = Module.finrank k V := by
        rw [← IntermediateField.finrank_fixedField_eq_card (F := k) (E := AdjoinRoot g) H]
        rw [Module.finrank_mul_finrank k (IntermediateField.fixedField H) (AdjoinRoot g)]
        rw [hFinF, hdeg_eq]
      have hdiv : Nat.card H ∣ Module.finrank k V :=
        ⟨Module.finrank k (IntermediateField.fixedField H), by rw [mul_comm]; exact h4.symm⟩
      have h5 : Nat.card H = Module.finrank k V := by
        rw [← Nat.div_mul_cancel hdiv, h3, one_mul]
      exact h5
    rw [← hcardP1, hHcard]
  -- (7) conclusion
  have hPcard : Nat.card P = Module.finrank k V := hP1_card P le_rfl hPne
  refine ⟨?_, ?_, ?_⟩
  · -- `|P|` is prime
    have hn2 : Module.finrank k V ≠ 1 := by
      intro h1
      have h3 : 1 < Nat.card ↥P := (Subgroup.one_lt_card_iff_ne_bot P).mpr hPne
      have h2 : Nat.card ↥P = 1 := by rw [hPcard]; exact h1
      omega
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn2
    haveI : Fact p.Prime := ⟨hp⟩
    have hpdvd' : p ∣ Nat.card ↥P := by rw [hPcard]; exact hpdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) p hpdvd'
    have hle : Subgroup.zpowers (x : V ≃ₗ[k] V) ≤ P := Subgroup.zpowers_le.mpr x.2
    have hne : Subgroup.zpowers (x : V ≃ₗ[k] V) ≠ ⊥ := by
      intro h
      have hmem : (x : V ≃ₗ[k] V) ∈ (⊥ : Subgroup (V ≃ₗ[k] V)) :=
        h ▸ Subgroup.mem_zpowers (x : V ≃ₗ[k] V)
      have h1 : (x : V ≃ₗ[k] V) = 1 := Subgroup.mem_bot.mp hmem
      have h2 : orderOf (x : V ≃ₗ[k] V) = 1 := by rw [h1, orderOf_one]
      have h3 : orderOf x = 1 := by simpa using h2
      have h4 : p = 1 := by rw [← hx]; exact h3
      exact hp.ne_one h4
    have hcard := hP1_card _ hle hne
    have hcz : Nat.card ↥(Subgroup.zpowers (x : V ≃ₗ[k] V)) = p := by
      rw [Nat.card_zpowers]
      simpa using hx
    rw [hcz] at hcard
    rw [hPcard]
    exact hcard ▸ hp
  · rw [hPcard, Module.natCard_eq_pow_finrank (K := k) (V := V)]
  · -- `C_U(v) = P` for `0 ≠ v ∈ C_V(P)`
    intro v hv hv0 u hu huv
    have hKle : P ≤ U ⊓ MulAction.stabilizer (V ≃ₗ[k] V) v := by
      refine le_inf hPU fun p hp => ?_
      rw [MulAction.mem_stabilizer_iff]
      exact hv p hp
    have hinjK : Function.Injective
        (fun z : ↥(U ⊓ MulAction.stabilizer (V ≃ₗ[k] V) v) => σhom ⟨z.1, z.2.1⟩) := by
      intro a b hab
      have key : ∀ m : AdjoinRoot g,
          (a : V ≃ₗ[k] V) (φa m v) = (b : V ≃ₗ[k] V) (φa m v) := by
        intro m
        have ha' := hσ_apply (a : V ≃ₗ[k] V) a.2.1 m v
        have hb' := hσ_apply (b : V ≃ₗ[k] V) b.2.1 m v
        have hav : (a : V ≃ₗ[k] V) v = v := (MulAction.mem_stabilizer_iff).mp a.2.2
        have hbv : (b : V ≃ₗ[k] V) v = v := (MulAction.mem_stabilizer_iff).mp b.2.2
        rw [hav] at ha'
        rw [hbv] at hb'
        rw [ha', hb']
        have hab' : σa (a : V ≃ₗ[k] V) a.2.1 m = σa (b : V ≃ₗ[k] V) b.2.1 m :=
          DFunLike.congr_fun hab m
        exact congrArg (fun z => φa z v) hab'
      refine Subtype.ext (LinearEquiv.ext fun x => ?_)
      obtain ⟨m, rfl⟩ := (hbij v hv0).2 x
      exact key m
    have hKcard : Nat.card ↥(U ⊓ MulAction.stabilizer (V ≃ₗ[k] V) v) ≤ Module.finrank k V := by
      have h1 : Nat.card ↥(U ⊓ MulAction.stabilizer (V ≃ₗ[k] V) v)
          ≤ Nat.card (AdjoinRoot g ≃ₐ[k] AdjoinRoot g) :=
        Nat.card_le_card_of_injective _ hinjK
      rwa [hgal_card] at h1
    have hPeqK : P = U ⊓ MulAction.stabilizer (V ≃ₗ[k] V) v :=
      Subgroup.eq_of_le_of_card_ge hKle (by rw [hPcard]; exact hKcard)
    have huK : u ∈ U ⊓ MulAction.stabilizer (V ≃ₗ[k] V) v := by
      rw [Subgroup.mem_inf]
      exact ⟨hu, (MulAction.mem_stabilizer_iff).mpr (by simpa using huv)⟩
    rw [hPeqK]
    exact huK

end Work.NormalComplement
