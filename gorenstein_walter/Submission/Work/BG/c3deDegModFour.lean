import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.lemma24
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.thm32
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.HatInjDefs
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterCompleteness

/-!
# Area BG: the degree of `χ` is divisible by `4` (BG 1981, Lemma 3.4, `|Λξ| ≠ 4` branch)

`Work.BG.c3deDegModFour` is the degree count of Bender–Glauberman 1981, p. 209, in the branch
of Lemma 3.4 where the third member `ξ` of `𝒮(χ) = bset C f χ = {ν, ν^s, ξ}` is `s`-fixed with
`|Λξ| ≠ 4` (so `|Λξ| = 2` by Remark 3.1) and `D.n = |Λν| = 4`.

The paper's argument: on `T = H₀ ∖ U` the coherent map (`Work.BG.lemma24`) gives the identity
`χ = ε·(ν + ν^s) + δ·ξ` with `ε = (χ, f ν) = ±1`, `δ = (χ, f ξ) = ±1`.  Hence
`Φ := χ|_{H₀} - ε·(ν + ν^s) - δ·ξ` is a virtual character of `H₀` vanishing on `T`, and

  `χ(1) = 2ε·ν(1) + δ·ξ(1) + Φ(1)`.

The substance is the divisibility `D.n ∣ Φ(1)` for every virtual character `Φ` of `H₀` vanishing
on `T` (`c3de_zIrr_apply_one_dvd` below): Fourier inversion writes `Φ = Σ_σ (Φ,σ)·σ` with the
coefficients `(Φ,σ)` constant along `Λ`-orbits (because `λ_β·Φ = Φ` for `Φ` supported on `U`),
so `Φ` is an integer combination of orbit sums, whose degrees `|Λσ|·σ(1)` are multiples of
`D.n` by Remark 3.1 (`Work.BG.rem31Shape`).  Finally `ν(1)` is odd (`ν|_U` is irreducible and
`U` has odd order) and `ξ(1) = 2·(odd)`, so `2ε·ν(1) + δ·ξ(1) ≡ 0 (mod 4)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

attribute [local instance] Classical.propDecidable

section Setup

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## 1. Elementary helpers -/

/-- `lamCF C β` takes the value `1` at the identity. -/
theorem c3de_lamCF_apply_one (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    lamCF C β (1 : ↥C.P.H0) = 1 := by
  rw [lamCF_apply, map_one, map_one, Units.val_one]

/-- `sconj` preserves the degree: `(ν^s)(1) = ν(1)`. -/
theorem c3de_sconj_apply_one (C : Sec2Ctx G) (φ : ClassFunction ↥C.P.H0 ℂ) :
    sconj C φ 1 = φ 1 := by
  rw [sconj, conjByH_apply, map_one]

/-- If `ψ` vanishes off `U`, then twisting by an inflated linear character does not change the
class-function inner product with `ψ`. -/
theorem c3de_inner_lamCF_mul (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {ψ : ClassFunction ↥C.P.H0 ℂ}
    (hvan : ∀ g : ↥C.P.H0, (g : G) ∉ C.P.U → ψ g = 0)
    (β : quotGroup C.P →* ℂˣ) (φ : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.inner ψ (lamCF C β * φ) = ClassFunction.inner ψ φ := by
  have hkey : ClassFunction.innerSum ψ (lamCF C β * φ) = ClassFunction.innerSum ψ φ := by
    simp only [ClassFunction.innerSum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    by_cases hg : (g : G) ∈ C.P.U
    · have h1 : lamCF C β g = 1 := by
        rw [lamCF_apply]
        have hq : quotMk C.P g = 1 :=
          (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) g).mpr hg
        rw [hq, map_one]
        rfl
      rw [ClassFunction.mul_apply, h1, one_mul]
    · rw [hvan g hg, zero_mul, zero_mul]
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.inner_eq_inv_card_mul_innerSum, hkey]

/-! ## 2. Degree form of Remark 3.1 -/

/-- Remark 3.1 in degree form: `D.n ∣ |Λr| · r(1)` for every `r ∈ Irr(H₀)`. -/
theorem c3de_ncard_lamOrbit_mul_apply_one_dvd (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (r : ClassFunction ↥C.P.H0 ℂ) (hr : IsIrreducibleCharacter r) :
    ∃ k : ℤ, ((lamOrbit C r).ncard : ℂ) * r 1 = (D.n : ℂ) * (k : ℂ) := by
  obtain ⟨a, hairr, hcase⟩ := rem31Shape D C hDC hS3 r hr
  obtain ⟨n, _hnpos, hn1⟩ := hr.exists_apply_one_eq_pos_natCast
  rcases hcase with ⟨_hres, hcard⟩ | ⟨a₂, _ha₂irr, _hne, hsame, hres, hcard2⟩
  · refine ⟨(n : ℤ), ?_⟩
    rw [hcard, hn1]
    push_cast
    ring
  · obtain ⟨m, _hmpos, hm1⟩ := hairr.exists_apply_one_eq_pos_natCast
    have hr1 : r 1 = (2 : ℂ) * (m : ℂ) := by
      have h := congrArg (fun f : ClassFunction ↥(Uin C) ℂ => f 1) hres
      rw [ClassFunction.add_apply, ClassFunction.restrict_apply, Subgroup.coe_one, hsame,
        hm1] at h
      rw [h]
      ring
    refine ⟨(m : ℤ), ?_⟩
    have hcast : (2 * (lamOrbit C r).ncard : ℂ) = (D.n : ℂ) := by
      exact_mod_cast hcard2
    rw [hr1]
    linear_combination (m : ℂ) * hcast

/-! ## 3. `ν(1)` is odd when `|Λν| = D.n` -/

/-- If `|Λν| = D.n` then `ν(1)` is odd (BG Remark 3.1 case (i) + odd order of `U`). -/
theorem c3de_nu_apply_one_odd (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    (hcard : (lamOrbit C ν).ncard = D.n) :
    ∃ n : ℕ, Odd n ∧ ν 1 = (n : ℂ) := by
  obtain ⟨a, hairr, hcase⟩ := rem31Shape D C hDC hS3 ν hν
  have hres : ClassFunction.restrict (Uin C) ν = a := by
    rcases hcase with h | h
    · exact h.1
    · obtain ⟨a₂, _, _, _, _, hcard2⟩ := h
      exfalso
      have := D.two_le
      omega
  have hUodd : Odd (Nat.card ↥(Uin C)) := by
    have h2 : Nat.card ↥(Uin C) = Nat.card ↥C.P.U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.P.U_le_H0).toEquiv
    rw [h2]
    exact odd_card_U_of_compat (D := D) hDC
  obtain ⟨n, _hnpos, hn1, hndvd⟩ := hairr.exists_natDegree_charValue_one_dvd_card
  refine ⟨n, hUodd.of_dvd_nat hndvd, ?_⟩
  have h := congrArg (fun f : ClassFunction ↥(Uin C) ℂ => f 1) hres
  rw [ClassFunction.restrict_apply, Subgroup.coe_one] at h
  rw [h, hn1]

/-! ## 4. Fibers of the orbit representative -/

/-- The fiber of `orbitRep C` over a representative `r` is the `Λ`-orbit of `r`. -/
theorem c3de_fiber_card (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Fintype (IrreducibleCharacter ↥C.P.H0)]
    (r : IrreducibleCharacter ↥C.P.H0) (hr : orbitRep C r = r) :
    (Finset.univ.filter (fun σ : IrreducibleCharacter ↥C.P.H0 => orbitRep C σ = r)).card
      = (lamOrbit C r.toClassFunction).ncard := by
  classical
  -- `orbitRep σ = r` iff `σ` is `Λ`-equivalent to `r`
  have hiff : ∀ σ : IrreducibleCharacter ↥C.P.H0,
      orbitRep C σ = r ↔ LamEquiv C r.toClassFunction σ.toClassFunction := by
    intro σ
    constructor
    · intro h
      have h1 := orbitRep_mem C σ
      rw [h] at h1
      exact s02c_LamEquiv_symm C h1
    · intro h
      have h1 : orbitRep C r = orbitRep C σ := orbitRep_eq_of_lamEquiv h
      rw [hr] at h1
      exact h1.symm
  have hfilt : (Finset.univ.filter (fun σ : IrreducibleCharacter ↥C.P.H0 => orbitRep C σ = r))
      = Finset.univ.filter (fun σ : IrreducibleCharacter ↥C.P.H0 =>
          LamEquiv C r.toClassFunction σ.toClassFunction) := by
    refine Finset.filter_congr ?_
    intro σ _
    exact hiff σ
  rw [hfilt]
  -- the fiber is in bijection (via `σ ↦ σ.toClassFunction`) with the `Λ`-orbit of `r`
  have hinj : Function.Injective
      (fun σ : IrreducibleCharacter ↥C.P.H0 => σ.toClassFunction) :=
    fun a b h => Subtype.ext h
  have hcard : (Finset.univ.filter (fun σ : IrreducibleCharacter ↥C.P.H0 =>
        LamEquiv C r.toClassFunction σ.toClassFunction)).card
      = ((Finset.univ.filter (fun σ : IrreducibleCharacter ↥C.P.H0 =>
        LamEquiv C r.toClassFunction σ.toClassFunction)).image
          (fun σ => σ.toClassFunction)).card :=
    (Finset.card_image_of_injective _ hinj).symm
  rw [hcard, ← Set.ncard_coe_finset]
  congr 1
  ext ν
  constructor
  · intro h
    obtain ⟨σ, hσ, hσν⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h)
    rw [← hσν]
    exact (mem_lamOrbit_iff C).mpr (Finset.mem_filter.mp hσ).2
  · intro hν
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨⟨ν, irreducible_of_mem_lamOrbit C hν r.2⟩, ?_, rfl⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_lamOrbit_iff C).mp hν⟩

/-! ## 5. The main divisibility: `D.n ∣ ψ(1)` for `ψ` vanishing on `T` -/

theorem c3de_zIrr_apply_one_dvd (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D)
    {ψ : ClassFunction ↥C.P.H0 ℂ} (hψ : ψ ∈ ZIrr ↥C.P.H0)
    (hvan : ∀ g : ↥C.P.H0, (g : G) ∉ C.P.U → ψ g = 0) :
    ∃ k : ℤ, ψ 1 = (D.n : ℂ) * (k : ℂ) := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  -- ## evaluation at `1` as a `ℂ`-linear map
  let ev : ClassFunction ↥C.P.H0 ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun z => z 1
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by simp [ClassFunction.smul_apply, smul_eq_mul] }
  have hev : ∀ z : ClassFunction ↥C.P.H0 ℂ, ev z = z 1 := fun _ => rfl
  -- ## Fourier expansion and its value at `1`
  have hfour : ψ = ∑ σ : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner ψ σ.toClassFunction • σ.toClassFunction :=
    (sum_inner_irreducibleCharacter_smul ψ).symm
  have hval : ψ 1 = ∑ σ : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner ψ σ.toClassFunction * (σ.toClassFunction 1) := by
    have hone : ∀ σ : IrreducibleCharacter ↥C.P.H0,
        ev (ClassFunction.inner ψ σ.toClassFunction • σ.toClassFunction)
          = ClassFunction.inner ψ σ.toClassFunction * (σ.toClassFunction 1) := by
      intro σ
      rw [map_smul]
      rw [smul_eq_mul, hev]
    have h := congrArg ev hfour
    rw [map_sum] at h
    simp only [hone] at h
    simpa only [hev] using h
  -- ## the transversal `orbitRep C`
  let rp : IrreducibleCharacter ↥C.P.H0 → IrreducibleCharacter ↥C.P.H0 := orbitRep C
  have hrp_mem : ∀ σ, LamEquiv C σ.toClassFunction (rp σ).toClassFunction :=
    fun σ => orbitRep_mem C σ
  have hrp_idem : ∀ σ, rp (rp σ) = rp σ := fun σ =>
    (orbitRep_eq_of_lamEquiv (hrp_mem σ)).symm
  -- ## the summand, constant on `Λ`-orbits
  let F : IrreducibleCharacter ↥C.P.H0 → ℂ := fun σ =>
    ClassFunction.inner ψ σ.toClassFunction * (σ.toClassFunction 1)
  have hF_rp : ∀ σ, F (rp σ) = F σ := by
    intro σ
    obtain ⟨β, hβ⟩ := hrp_mem σ
    have h1 : ClassFunction.inner ψ (rp σ).toClassFunction
        = ClassFunction.inner ψ σ.toClassFunction := by
      rw [hβ, c3de_inner_lamCF_mul C hvan β σ.toClassFunction]
    have h2 : (rp σ).toClassFunction 1 = σ.toClassFunction 1 := by
      rw [hβ, ClassFunction.mul_apply, c3de_lamCF_apply_one, one_mul]
    simp only [F, h1, h2]
  -- ## regroup over the fibers of `rp`
  have hregroup : (∑ σ : IrreducibleCharacter ↥C.P.H0, F σ)
      = ∑ r ∈ (Finset.univ.image rp),
          ∑ σ ∈ (Finset.univ.filter
            (fun σ : IrreducibleCharacter ↥C.P.H0 => rp σ = r)), F r := by
    have h1 : (∑ σ : IrreducibleCharacter ↥C.P.H0, F σ)
        = ∑ σ : IrreducibleCharacter ↥C.P.H0, F (rp σ) :=
      Finset.sum_congr rfl (fun σ _ => (hF_rp σ).symm)
    rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image rp)
      (g := rp) (f := fun σ => F (rp σ))
      (fun σ _ => Finset.mem_image_of_mem rp (Finset.mem_univ σ))]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun σ hσ => ?_))
    rw [(Finset.mem_filter.mp hσ).2]
  -- ## each fiber sum is `card · F r`
  have hfiber : ∀ r ∈ Finset.univ.image rp,
      (∑ σ ∈ (Finset.univ.filter
          (fun σ : IrreducibleCharacter ↥C.P.H0 => rp σ = r)), F r)
        = ((Finset.univ.filter
            (fun σ : IrreducibleCharacter ↥C.P.H0 => rp σ = r)).card : ℂ) * F r := by
    intro r _
    rw [Finset.sum_const, nsmul_eq_mul]
  -- ## each fiber term is a multiple of `D.n`
  have hterm : ∀ r ∈ Finset.univ.image rp,
      ∃ k : ℤ, ((Finset.univ.filter
            (fun σ : IrreducibleCharacter ↥C.P.H0 => rp σ = r)).card : ℂ) * F r
          = (D.n : ℂ) * (k : ℂ) := by
    intro r hr
    have hrf : rp r = r := by
      obtain ⟨ρ, -, hρ⟩ := Finset.mem_image.mp hr
      rw [← hρ, hrp_idem]
    have hcard : (Finset.univ.filter
          (fun σ : IrreducibleCharacter ↥C.P.H0 => rp σ = r)).card
        = (lamOrbit C r.toClassFunction).ncard := c3de_fiber_card C r hrf
    obtain ⟨k₁, hk₁⟩ := c3de_ncard_lamOrbit_mul_apply_one_dvd D C hDC hS3 r.toClassFunction r.2
    obtain ⟨m, hm⟩ := mem_ZIrr_inner_int r hψ
    refine ⟨m * k₁, ?_⟩
    rw [hcard]
    simp only [F]
    rw [hm]
    push_cast
    linear_combination (m : ℂ) * hk₁
  -- ## assemble
  let kf : IrreducibleCharacter ↥C.P.H0 → ℤ := fun r =>
    if h : r ∈ Finset.univ.image rp then (hterm r h).choose else 0
  have hkf : ∀ r (h : r ∈ Finset.univ.image rp),
      ((Finset.univ.filter
            (fun σ : IrreducibleCharacter ↥C.P.H0 => rp σ = r)).card : ℂ) * F r
          = (D.n : ℂ) * ((kf r : ℤ) : ℂ) := by
    intro r h
    simp only [kf, dif_pos h]
    exact (hterm r h).choose_spec
  refine ⟨∑ r ∈ Finset.univ.image rp, kf r, ?_⟩
  rw [hval, hregroup]
  have hfinal : ∑ r ∈ Finset.univ.image rp,
        (∑ σ ∈ (Finset.univ.filter
          (fun σ : IrreducibleCharacter ↥C.P.H0 => rp σ = r)), F r)
      = ∑ r ∈ Finset.univ.image rp, (D.n : ℂ) * ((kf r : ℤ) : ℂ) := by
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [hfiber r hr]
    exact hkf r hr
  rw [hfinal]
  push_cast
  rw [Finset.mul_sum]

end Setup

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- BG 1981, p. 209, degree count in the `|Λξ| ≠ 4` branch of Lemma 3.4: with
`𝒮(χ) = {ν, ν^s, ξ}`, `D.n = 4` and `ξ 1 = 2 m` (`m` odd), one has `4 ∣ χ(1)`. -/
theorem c3deDegModFour {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      D.n = 4 →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
        Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 →
        Work.GW2.C16.bset C f χ = {ν, Work.BG.sconj C ν, ξ} →
        (∃ m : ℤ, ξ 1 = (2 : ℂ) * (m : ℂ) ∧ Odd m) →
        ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) := by
  intro hDC hS3 f hf χ hχ ν hν hne _hdisj h4ν _hinv hn4
        ξ hξ hξν hξνs hξs _hξ4 hbset hξdeg
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  obtain ⟨hνirr, hνne0⟩ := hν
  obtain ⟨hξirr, hξne0⟩ := hξ
  -- ## the coherence data at `ν`: `‖f ν‖ = 1` (since `ν^s ≠ ν`) and `(χ, f ν) = ±1`
  have hkeyν : ν ∈ orbitKey C ν := Or.inl (s02c_LamEquiv_refl C ν)
  obtain ⟨hZIfν, hfνs, hnormfν, -, -, -⟩ := (hf.1 ν hνirr) ν hkeyν ν hkeyν hνirr hνirr
  have hnormfν1 : ClassFunction.inner (f ν) (f ν) = 1 := by rw [hnormfν]; simp [hne]
  have hνpair : ClassFunction.inner χ (f ν) = 1 ∨ ClassFunction.inner χ (f ν) = -1 :=
    inner_pmIrr_eq_pm_one hZIfν (Or.inl hnormfν1) hχ hνne0
  -- ## the coherence data at `ξ`: `‖f ξ‖ = 2` (since `ξ^s = ξ`) and `(χ, f ξ) = ±1`
  have hkeyξ : ξ ∈ orbitKey C ξ := Or.inl (s02c_LamEquiv_refl C ξ)
  obtain ⟨hZIfξ, -, hnormfξ, -, -, -⟩ := (hf.1 ξ hξirr) ξ hkeyξ ξ hkeyξ hξirr hξirr
  have hnormfξ2 : ClassFunction.inner (f ξ) (f ξ) = 2 := by rw [hnormfξ]; simp [hξs]
  have hξpair : ClassFunction.inner χ (f ξ) = 1 ∨ ClassFunction.inner χ (f ξ) = -1 :=
    inner_pmIrr_eq_pm_one hZIfξ (Or.inr hnormfξ2) hχ hξne0
  -- ## `Φ := χ|_{H₀} - ε·(ν + ν^s) - δ·ξ` vanishes on `T = H₀ ∖ U`
  set Φ : ClassFunction ↥C.P.H0 ℂ :=
    ClassFunction.restrict C.P.H0 χ
      - (ClassFunction.inner χ (f ν)) • (ν + sconj C ν)
      - (ClassFunction.inner χ (f ξ)) • ξ with hΦdef
  have hΦzero : ∀ g : ↥C.P.H0, (g : G) ∉ C.P.U → Φ g = 0 := by
    intro g hg
    have h24 := (lemma24 C f hf χ hχ).2.1 g hg
    have hdist1 : ν ∉ (insert (sconj C ν) ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hne h.symm, fun h => hξν h.symm⟩
    have hdist2 : sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      simp only [Set.mem_singleton_iff]
      exact fun h => hξνs h.symm
    rw [hbset,
      show ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ))
          = insert ν (insert (sconj C ν) ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) from rfl,
      finsum_mem_insert _ hdist1 (Set.toFinite _),
      finsum_mem_insert _ hdist2 (Set.toFinite _),
      finsum_mem_singleton, hfνs] at h24
    rw [hΦdef]
    simp only [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.add_apply,
      ClassFunction.restrict_apply]
    rw [h24]
    ring
  -- ## `Φ ∈ ℤ[Irr(H₀)]`
  have hΦZI : Φ ∈ ZIrr ↥C.P.H0 := by
    have h1 : ClassFunction.restrict C.P.H0 χ ∈ ZIrr ↥C.P.H0 :=
      ClassFunction.restrict_mem_ZIrr C.P.H0 (mem_ZIrr_of_isPmIrr hχ)
    have h2 : ν + sconj C ν ∈ ZIrr ↥C.P.H0 :=
      Submodule.add_mem _ (IsIrreducibleCharacter.mem_ZIrr hνirr)
        (by simpa only [sconj] using
          (IsIrreducibleCharacter.mem_ZIrr (IsIrreducibleCharacter.conjByH C.P C.s hνirr)))
    have h3 : ξ ∈ ZIrr ↥C.P.H0 := IsIrreducibleCharacter.mem_ZIrr hξirr
    have h2' : (ClassFunction.inner χ (f ν)) • (ν + sconj C ν) ∈ ZIrr ↥C.P.H0 := by
      rcases hνpair with h | h
      · rw [h, one_smul]; exact h2
      · rw [h, neg_one_smul]; exact Submodule.neg_mem _ h2
    have h3' : (ClassFunction.inner χ (f ξ)) • ξ ∈ ZIrr ↥C.P.H0 := by
      rcases hξpair with h | h
      · rw [h, one_smul]; exact h3
      · rw [h, neg_one_smul]; exact Submodule.neg_mem _ h3
    rw [hΦdef]
    exact Submodule.sub_mem (ZIrr ↥C.P.H0) (Submodule.sub_mem (ZIrr ↥C.P.H0) h1 h2') h3'
  -- ## `D.n ∣ Φ(1)`
  obtain ⟨k, hk⟩ := c3de_zIrr_apply_one_dvd D C hDC hS3 hΦZI hΦzero
  -- ## `ν(1)` is odd, `ξ(1) = 2m'` with `m'` odd
  obtain ⟨d, hdodd, hd1⟩ :=
    c3de_nu_apply_one_odd D C hDC hS3 hνirr (by rw [h4ν, hn4])
  obtain ⟨m', hm'1, hm'odd⟩ := hξdeg
  -- ## evaluate `Φ` at `1`
  have hΦ1 := congrArg (fun z : ClassFunction ↥C.P.H0 ℂ => z 1) hΦdef
  simp only [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.add_apply,
    ClassFunction.restrict_apply, Subgroup.coe_one, c3de_sconj_apply_one] at hΦ1
  rw [hk] at hΦ1
  have hχ1 : χ 1 = (ClassFunction.inner χ (f ν)) * (2 * (d : ℂ))
      + (ClassFunction.inner χ (f ξ)) * (2 * (m' : ℂ)) + (D.n : ℂ) * (k : ℂ) := by
    rw [hd1, hm'1] at hΦ1
    rw [hΦ1]
    ring
  -- ## `2ε·ν(1) + δ·ξ(1)` is divisible by `4`
  have hmain : ∃ K : ℤ, (ClassFunction.inner χ (f ν)) * (2 * (d : ℂ))
      + (ClassFunction.inner χ (f ξ)) * (2 * (m' : ℂ)) = 4 * (K : ℂ) := by
    obtain ⟨u, hu⟩ := hdodd
    obtain ⟨v, hv⟩ := hm'odd
    rcases hνpair with h1 | h1 <;> rcases hξpair with h2 | h2
    · exact ⟨(u : ℤ) + v + 1, by rw [h1, h2, hu, hv]; push_cast; ring⟩
    · exact ⟨(u : ℤ) - v, by rw [h1, h2, hu, hv]; push_cast; ring⟩
    · exact ⟨v - (u : ℤ), by rw [h1, h2, hu, hv]; push_cast; ring⟩
    · exact ⟨-((u : ℤ) + v + 1), by rw [h1, h2, hu, hv]; push_cast; ring⟩
  obtain ⟨K, hK⟩ := hmain
  have hD4 : (D.n : ℂ) = 4 := by rw [hn4]; norm_num
  refine ⟨K + k, ?_⟩
  rw [hχ1, hK, hD4]
  push_cast
  ring

end Work.BG
