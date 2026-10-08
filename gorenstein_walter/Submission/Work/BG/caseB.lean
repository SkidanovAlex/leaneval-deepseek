import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.Sec4Extra
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.hatInj
import Submission.Work.BG.deltaShape
import Submission.Work.BG.Hat
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.l41vBInv
import Submission.Work.BG.L41Aux
import Submission.Work.BG.caseBC.comb413Self
import Submission.Work.BG.caseBC.lemma42Self
import Submission.Work.BG.s4L41
import Submission.Work.BG.congContra

set_option linter.unusedSectionVars false

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 Subgroup

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
  (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

/-! ## 0. Parity helpers -/

theorem caseB_zmod2_eq_one_of_odd {m : ℤ} (h : Odd m) : (m : ZMod 2) = 1 := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul, zero_add]

theorem caseB_odd_of_zmod2_eq_one {m : ℤ} (h : (m : ZMod 2) = 1) : Odd m := by
  have h1 : ((m - 1 : ℤ) : ZMod 2) = 0 := by push_cast; rw [h]; ring
  have hdvd : (2 : ℤ) ∣ m - 1 := by
    have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd (m - 1) 2).mp h1
    simpa using h'
  obtain ⟨q, hq⟩ := hdvd
  exact ⟨q, by omega⟩

theorem caseB_exists_odd_of_odd_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (h : Odd (∑ i ∈ s, f i)) : ∃ i ∈ s, Odd (f i) := by
  by_contra hno
  push_neg at hno
  have hz : ((∑ i ∈ s, f i : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_sum]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have he : Even (f i) := by
      rcases Int.even_or_odd (f i) with he | ho
      · exact he
      · exact absurd ho (hno i hi)
    obtain ⟨q, hq⟩ := even_iff_two_dvd.mp he
    rw [hq]; push_cast
    have h2' : (2 : ZMod 2) = 0 := by decide
    rw [h2', zero_mul]
  rw [caseB_zmod2_eq_one_of_odd h] at hz
  exact absurd hz (by decide)

theorem caseB_odd_of_odd_mul {a b : ℤ} (h : Odd (a * b)) : Odd a := by
  rcases Int.even_or_odd a with he | ho
  · exfalso
    obtain ⟨q, hq⟩ := even_iff_two_dvd.mp he
    have hev : Even (a * b) := by
      rw [hq]
      exact ⟨b * q, by ring⟩
    exact Int.not_even_iff_odd.mpr h hev
  · exact ho

/-! ## 1. Elementary `λ₂`-facts -/

theorem caseB_lamCF_one {β₂ : quotGroup C.P →* ℂˣ} : lamCF C β₂ 1 = 1 := by
  simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]

theorem caseB_lam_two_mul_notMem_S4Index {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {x : ClassFunction ↥C.P.H0 ℂ} (hx : x ∈ S4Index C) :
    lamCF C β₂ * x ∉ S4Index C := by
  intro h
  have hxt : ((lamCF C β₂ * x) C.t) = ((lamCF C β₂ * x) 1) := h.2.2
  rw [ClassFunction.mul_apply, ClassFunction.mul_apply, lamCF_two_apply_t C h2 hβ,
    caseB_lamCF_one C (β₂ := β₂), hx.2.2] at hxt
  have hx1 : x 1 ≠ 0 := by
    obtain ⟨d, hd, h1⟩ := hx.1.exists_apply_one_eq_pos_natCast
    rw [h1]; exact_mod_cast hd.ne'
  apply hx1
  have h : -(x 1) = x 1 := by simpa using hxt
  have h2' : (2:ℂ) * x 1 = 0 := by linear_combination (-1:ℂ) * h
  exact (mul_eq_zero.mp h2').resolve_left (by norm_num)

theorem caseB_lam_mul_cancel {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) :
    Function.Injective (fun x : ClassFunction ↥C.P.H0 ℂ => lamCF C β₂ * x) := by
  intro x y hxy
  have hkey : ∀ z, lamCF C β₂ * (lamCF C β₂ * z) = z := fun z => by
    rw [← mul_assoc_cf, Work.BG.lamCF_two_mul_self C h2, one_mul_cf]
  have := congrArg (fun z => lamCF C β₂ * z) hxy
  rwa [hkey x, hkey y] at this

/-! ## 2. The `δ`'s of `S4Index` form an orthogonal family -/

theorem caseB_delta_orthogonal (hc : Compat D C) (hn : D.n = 2)
    {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {ν μ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C) (hμ : μ ∈ S4Index C)
    (hne : ν ≠ μ) :
    ClassFunction.inner (delta C β₂ ν) (delta C β₂ μ) = 0 := by
  classical
  have h2 := quotGroup_card_two D C hc hn
  have hirrν := hν.1
  have hirrμ := hμ.1
  have hlamν := lam_two_mul_irr C (β₂ := β₂) hirrν
  have hlamμ := lam_two_mul_irr C (β₂ := β₂) hirrμ
  have hgram := s02_gram C ν (lamCF C β₂ * ν) μ (lamCF C β₂ * μ) hirrν hlamν hirrμ hlamμ
    ⟨β₂, rfl⟩ ⟨β₂, rfl⟩
  have hνs : sconj C ν = ν := hν.2.1
  have hμs : sconj C μ = μ := hμ.2.1
  have hsν : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν := by
    rw [sconj_lam_two_mul C h2 hβ ν, hνs]
  have hneμν : μ ≠ ν := hne.symm
  have hne_lamμ_ν : lamCF C β₂ * μ ≠ ν := fun h =>
    caseB_lam_two_mul_notMem_S4Index C h2 hβ hμ (h ▸ hν)
  have hne_μ_lamν : μ ≠ lamCF C β₂ * ν := fun h =>
    caseB_lam_two_mul_notMem_S4Index C h2 hβ hν (h ▸ hμ)
  have hne_lamlam : lamCF C β₂ * μ ≠ lamCF C β₂ * ν := fun h =>
    hne ((caseB_lam_mul_cancel C h2 h).symm)
  have hA : cH C ν μ = 0 := by
    rw [Work.BG.cH]; simp [hneμν, hνs]
  have hB : cH C ν (lamCF C β₂ * μ) = 0 := by
    rw [Work.BG.cH]; simp [hne_lamμ_ν, hνs]
  have hCeq : cH C (lamCF C β₂ * ν) μ = 0 := by
    rw [Work.BG.cH]; simp [hne_μ_lamν, hsν]
  have hDeq : cH C (lamCF C β₂ * ν) (lamCF C β₂ * μ) = 0 := by
    rw [Work.BG.cH]; simp [hne_lamlam, hsν]
  show ClassFunction.inner (ind C (ν - lamCF C β₂ * ν)) (ind C (μ - lamCF C β₂ * μ)) = 0
  rw [hgram, hA, hB, hCeq, hDeq]
  ring

theorem caseB_delta_injective (hc : Compat D C) (hn : D.n = 2)
    {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {ν μ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C) (hμ : μ ∈ S4Index C)
    (h : delta C β₂ ν = delta C β₂ μ) : ν = μ := by
  by_contra hne
  have h2 := quotGroup_card_two D C hc hn
  have horth := caseB_delta_orthogonal D C hc hn hβ hν hμ hne
  rw [h, l41_delta_inner_self C h2 hβ hμ.1, if_pos hμ.2.1] at horth
  norm_num at horth

/-! ## 3. `NSFixed` and `NSConj` interact trivially -/

/-- If `B` is normalised by `N_G(S)`, an `N_G(S)`-fixed hat has no proper conjugate. -/
theorem caseB_NSConj_eq_of_NSFixed
    (hBinv : ∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    {θ θ' : ClassFunction ↥D.B ℂ} (hfix : NSFixed D θ) (hconj : NSConj D θ θ') :
    θ' = θ := by
  obtain ⟨x, hx, hc⟩ := hconj
  ext b
  have hb' := hBinv x hx b b.2
  have h1 : θ' b = θ ⟨x⁻¹ * (b : G) * x, hb'⟩ := hc b ⟨x⁻¹ * (b : G) * x, hb'⟩ rfl
  have h2 : θ b = θ ⟨x⁻¹ * (b : G) * x, hb'⟩ := hfix x hx b ⟨x⁻¹ * (b : G) * x, hb'⟩ rfl
  rw [h1, ← h2]

/-! ## 4. Two membership facts for `𝒮'(χ) = bset'` -/

/-- `bset'` membership only depends on the non-vanishing of the inner product, in either
orientation, together with `S4Index`. -/
theorem caseB_mem_bset_iff {β₂ : quotGroup C.P →* ℂˣ}
    {χ : ClassFunction G ℂ} {ν : ClassFunction ↥C.P.H0 ℂ} :
    ν ∈ bset' C β₂ χ ↔
      ν ∈ S4Index C ∧ ClassFunction.inner (delta C β₂ ν) χ ≠ 0 := by
  rw [Work.GW2.C16.bset']
  constructor
  · rintro ⟨hS, h⟩
    exact ⟨hS, fun h0 => h (by rw [ClassFunction.inner_star_comm, h0, star_zero])⟩
  · rintro ⟨hS, h⟩
    exact ⟨hS, fun h0 => h (by rw [ClassFunction.inner_star_comm, h0, star_zero])⟩

/-- If `𝒮'(χ)` meets the component `J` of `ν₀`, then it is contained in `J`: any other member
shares the constituent `χ` with a member of `J`, hence is adjacent to it. -/
theorem caseB_bset'_mem_J (hc : Compat D C) (hn : D.n = 2)
    {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {ν₀ : ClassFunction ↥C.P.H0 ℂ} (hν₀ : ν₀ ∈ S4Index C)
    (χ : IrreducibleCharacter G)
    {z : ClassFunction ↥C.P.H0 ℂ} (hz : z ∈ bset' C β₂ (χ : ClassFunction G ℂ))
    (hzJ : Conn C β₂ ν₀ z)
    {y : ClassFunction ↥C.P.H0 ℂ} (hy : y ∈ bset' C β₂ (χ : ClassFunction G ℂ)) :
    Conn C β₂ ν₀ y := by
  rw [caseB_mem_bset_iff] at hy hz
  rcases hy with ⟨hyS, hyne⟩
  rcases hz with ⟨hzS, hzne⟩
  rcases eq_or_ne y z with h | h
  · rw [h]; exact hzJ
  · refine hzJ.tail ⟨hzS, hyS, ?_, ?_⟩
    · intro heq
      exact h (caseB_delta_injective D C hc hn hβ hyS hzS heq.symm)
    · intro hdisj
      rcases hdisj χ with hh | hh
      · exact hzne hh
      · exact hyne hh

/-! ## 6. The assembly of `CaseBProp` from the four §4 leaves -/

theorem caseB_of_leaves (hComb : Work.GW2.C23.Comb413Prop)
    (h41 : Work.GW2.C16.Lemma41Prop D C)
    (h42 : Work.GW2.C23.Lemma42Prop D C)
    (hCC : Work.GW2.C23.CongContraProp D C) :
    Work.GW2.C23.CaseBProp D C := by
  classical
  intro hc hn β₂ hβ ν₀ hν₀ hall μ₀ hAdj
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  have hBinv := l41vBInv D hn
  haveI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  -- the component `J` of `ν₀`
  let J : Set (ClassFunction ↥C.P.H0 ℂ) := {μ | Conn C β₂ ν₀ μ}
  have hJsub : J ⊆ S4Index C := by
    intro μ hμ
    induction hμ with
    | refl => exact hν₀
    | tail hprev hrel ih => exact hrel.2.1
  have hν₀J : ν₀ ∈ J := Relation.ReflTransGen.refl
  have hμ₀J : μ₀ ∈ J := Relation.ReflTransGen.single hAdj
  -- finiteness of `J` (it injects into `Irr(H₀)`)
  haveI : Finite (IrreducibleCharacter ↥C.P.H0) := finite_irreducibleCharacter
  haveI : Finite ↥(S4Index C) :=
    Finite.of_injective
      (fun x : ↥(S4Index C) => (⟨x.1, x.2.1⟩ : IrreducibleCharacter ↥C.P.H0))
      (fun a b h => Subtype.ext (congrArg (fun z : IrreducibleCharacter ↥C.P.H0 => z.1) h))
  haveI : Finite ↥J :=
    Finite.of_injective
      (fun x : ↥J => (⟨x.1, (hJsub x.2).1⟩ : IrreducibleCharacter ↥C.P.H0))
      (fun a b h => Subtype.ext (congrArg (fun z : IrreducibleCharacter ↥C.P.H0 => z.1) h))
  haveI : Fintype ↥J := Fintype.ofFinite _
  have hS4fin : (S4Index C).Finite := Set.toFinite _
  -- the matrix of inner products
  let v : ↥J → IrreducibleCharacter G → ℤ := fun j χ =>
    (mem_ZIrr_inner_int χ (l41_delta_mem_ZIrr C (β₂ := β₂) (hJsub j.2).1)).choose
  have hv : ∀ (j : ↥J) (χ : IrreducibleCharacter G),
      ClassFunction.inner (delta C β₂ j.1) (χ : ClassFunction G ℂ) = (v j χ : ℂ) :=
    fun j χ =>
      (mem_ZIrr_inner_int χ (l41_delta_mem_ZIrr C (β₂ := β₂) (hJsub j.2).1)).choose_spec
  have hv0 : ∀ (j : ↥J) (χ : IrreducibleCharacter G),
      v j χ = 0 ↔
        ClassFunction.inner (delta C β₂ j.1) (χ : ClassFunction G ℂ) = 0 := by
    intro j χ
    constructor
    · intro h; rw [hv j χ, h]; norm_num
    · intro h; exact Int.cast_eq_zero.mp (by rw [← hv j χ, h])
  have hvne : ∀ (j : ↥J) (χ : IrreducibleCharacter G),
      v j χ ≠ 0 ↔
        ClassFunction.inner (delta C β₂ j.1) (χ : ClassFunction G ℂ) ≠ 0 :=
    fun j χ => (hv0 j χ).not
  -- (h1) rows have support 4 and entries in `{0, ±1}`
  have h1 : ∀ j : ↥J,
      (Finset.univ.filter (fun i => v j i ≠ 0)).card = 4 ∧ ∀ i, (v j i) ^ 2 ≤ 1 := by
    intro j
    obtain ⟨T, hTcard, hTin, hTout⟩ := deltaShape D C hc hn β₂ hβ j.1 (hJsub j.2)
    have hval : ∀ χ : IrreducibleCharacter G, v j χ = 1 ∨ v j χ = -1 ∨ v j χ = 0 := by
      intro χ
      by_cases hmem : χ ∈ T
      · rcases hTin χ hmem with h | h
        · exact Or.inl (Int.cast_injective (by rw [← hv j χ, h]; norm_num))
        · exact Or.inr (Or.inl (Int.cast_injective (by rw [← hv j χ, h]; norm_num)))
      · exact Or.inr (Or.inr ((hv0 j χ).mpr (hTout χ hmem)))
    have hfilter : (Finset.univ.filter (fun i : IrreducibleCharacter G => v j i ≠ 0)) = T := by
      ext χ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hχ
        by_contra hc'
        exact hχ ((hv0 j χ).mpr (hTout χ hc'))
      · intro hχ
        rcases hTin χ hχ with h | h
        · rw [hvne j χ, h]; norm_num
        · rw [hvne j χ, h]; norm_num
    refine ⟨by rw [hfilter, hTcard], fun χ => ?_⟩
    rcases hval χ with h | h | h <;> rw [h] <;> norm_num
  -- (h2) distinct rows are orthogonal
  have h2orth : ∀ j k : ↥J, j ≠ k → ∑ χ : IrreducibleCharacter G, v j χ * v k χ = 0 := by
    intro j k hjk
    have hjk' : j.1 ≠ k.1 := fun h => hjk (Subtype.ext h)
    have horth := caseB_delta_orthogonal D C hc hn hβ (hJsub j.2) (hJsub k.2) hjk'
    have hcast : ((∑ χ : IrreducibleCharacter G, v j χ * v k χ : ℤ) : ℂ)
        = ClassFunction.inner (delta C β₂ j.1) (delta C β₂ k.1) := by
      rw [Int.cast_sum,
        OddOrder.Peterfalvi.S12.mem_ZIrr_inner_eq_sum_over_irr
          (l41_delta_mem_ZIrr C (β₂ := β₂) (hJsub k.2).1)]
      exact Finset.sum_congr rfl (fun χ _ => by push_cast; rw [hv j χ, hv k χ])
    rw [horth] at hcast
    exact Int.cast_eq_zero.mp hcast
  -- (h3) every column has size 0, 1 or 3
  have h3 : ∀ χ : IrreducibleCharacter G,
      (Finset.univ.filter (fun j : ↥J => v j χ ≠ 0)).card ∈ ({0,1,3} : Finset ℕ) := by
    intro χ
    have hSsub : bset' C β₂ (χ : ClassFunction G ℂ) ⊆ S4Index C := by
      intro y hy
      rw [caseB_mem_bset_iff] at hy
      exact hy.1
    have hSfin : (bset' C β₂ (χ : ClassFunction G ℂ)).Finite := hS4fin.subset hSsub
    have hSJfin : (bset' C β₂ (χ : ClassFunction G ℂ) ∩ J).Finite :=
      hSfin.subset Set.inter_subset_left
    have hncard :
        (bset' C β₂ (χ : ClassFunction G ℂ) ∩ J).ncard ∈ ({0,1,3} : Finset ℕ) := by
      by_cases hne : (bset' C β₂ (χ : ClassFunction G ℂ) ∩ J).Nonempty
      · have hsubJ : bset' C β₂ (χ : ClassFunction G ℂ) ⊆ J := by
          intro y hy
          obtain ⟨z, hzS, hzJ⟩ := hne
          exact caseB_bset'_mem_J D C hc hn hβ hν₀ χ hzS hzJ hy
        have heq : bset' C β₂ (χ : ClassFunction G ℂ) ∩ J
            = bset' C β₂ (χ : ClassFunction G ℂ) := Set.inter_eq_left.mpr hsubJ
        rw [heq]
        have hSne : (bset' C β₂ (χ : ClassFunction G ℂ)).Nonempty :=
          hne.mono Set.inter_subset_left
        rcases (h41 hc hn β₂ hβ (χ : ClassFunction G ℂ) (Or.inl χ.isIrreducible) hSne).1 with
          h | h <;> simp [h]
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
    have hcard : ∀ y : ClassFunction ↥C.P.H0 ℂ,
        y ∈ bset' C β₂ (χ : ClassFunction G ℂ) ∩ J ↔
          ∃ j : ↥J, j.1 = y ∧ v j χ ≠ 0 := by
      intro y
      constructor
      · rintro ⟨hyS, hyJ⟩
        rw [caseB_mem_bset_iff] at hyS
        exact ⟨⟨y, hyJ⟩, rfl, (hvne ⟨y, hyJ⟩ χ).mpr hyS.2⟩
      · rintro ⟨j, rfl, hvj⟩
        refine ⟨?_, j.2⟩
        rw [caseB_mem_bset_iff]
        exact ⟨hJsub j.2, (hvne j χ).mp hvj⟩
    set T' : Finset ↥J := Finset.univ.filter (fun j : ↥J => v j χ ≠ 0) with hT'def
    have hT'mem : ∀ j : ↥J, j ∈ T' ↔ v j χ ≠ 0 := by intro j; rw [hT'def]; simp
    have himg : T'.image (Subtype.val : ↥J → ClassFunction ↥C.P.H0 ℂ) = hSJfin.toFinset := by
      ext y
      rw [Finset.mem_image, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact (hcard j.1).mpr ⟨j, rfl, (hT'mem j).mp hj⟩
      · intro hy
        obtain ⟨j, hj1, hvj⟩ := (hcard y).mp hy
        exact ⟨j, (hT'mem j).mpr hvj, hj1⟩
    have hcardT' : T'.card = (bset' C β₂ (χ : ClassFunction G ℂ) ∩ J).ncard := by
      rw [← Finset.card_image_of_injective T' (Subtype.val_injective), himg,
        ← Set.ncard_eq_toFinset_card _ hSJfin]
    rw [hcardT']
    exact hncard
  -- (h4) the rows are `F₂`-independent
  have h4 : ∀ n : ↥J → ℤ, (∃ j, Odd (n j)) →
      ∃ χ : IrreducibleCharacter G, Odd (∑ j, n j * v j χ) := by
    intro n hn'
    obtain ⟨j₀, hj₀odd⟩ := hn'
    have hμ₀ : j₀.1 ∈ S4Index C := hJsub j₀.2
    let θμ : ClassFunction ↥D.B ℂ := Classical.choose ((Hat D C hc hn j₀.1 hμ₀).1)
    have hθμ : HatOf D C j₀.1 θμ := Classical.choose_spec ((Hat D C hc hn j₀.1 hμ₀).1)
    obtain ⟨μ', hμ'Z, hμ'prop⟩ := h42 hc hn β₂ hβ j₀.1 hμ₀ θμ hθμ
    have hk : ∀ j : ↥J, ∃ (θj : ClassFunction ↥D.B ℂ) (k : ℤ),
        HatOf D C j.1 θj ∧ ClassFunction.inner (delta C β₂ j.1) μ' = (k : ℂ) ∧
          (Odd k ↔ NSConj D θj θμ) := by
      intro j
      obtain ⟨θj, hθj⟩ := (Hat D C hc hn j.1 (hJsub j.2)).1
      obtain ⟨k, hkv, hkodd⟩ := hμ'prop j.1 (hJsub j.2) θj hθj
      exact ⟨θj, k, hθj, hkv, hkodd⟩
    choose θF kF hF using hk
    have hparity : ∀ j : ↥J, Odd (kF j) ↔ j = j₀ := by
      intro j
      constructor
      · intro hodd
        have hnc : NSConj D (θF j) θμ := (hF j).2.2.mp hodd
        have hfixj : NSFixed D (θF j) := hall j.1 j.2 (θF j) (hF j).1
        have heq : θμ = θF j := caseB_NSConj_eq_of_NSFixed D hBinv hfixj hnc
        have h1 : j.1 = j₀.1 :=
          hatInj D C hc hn j.1 (hJsub j.2) j₀.1 hμ₀ (θF j) (hF j).1 (heq ▸ hθμ)
        exact Subtype.ext h1
      · intro hj
        rw [hj]
        have heq : θF j₀ = θμ :=
          (Hat D C hc hn j₀.1 hμ₀).2 (θF j₀) θμ (hF j₀).1 hθμ
        refine (hF j₀).2.2.mpr ⟨1, Subgroup.one_mem _, fun b b' h => ?_⟩
        have hbb : b' = b := Subtype.ext (by simpa using h)
        rw [hbb, heq]
    -- the virtual character `Ψ = Σ_j n_j δ_j`
    let Ψ : ClassFunction G ℂ := ∑ j : ↥J, (n j : ℂ) • delta C β₂ j.1
    have hΨZ : Ψ ∈ ZIrr G := by
      have hsum : Ψ = ∑ j : ↥J, (n j) • delta C β₂ j.1 := by
        rw [show Ψ = ∑ j : ↥J, (n j : ℂ) • delta C β₂ j.1 from rfl]
        exact Finset.sum_congr rfl (fun j _ => Int.cast_smul_eq_zsmul ℂ (n j) _)
      rw [hsum]
      exact Submodule.sum_mem _ (fun j _ =>
        Submodule.smul_mem _ (n j) (l41_delta_mem_ZIrr C (β₂ := β₂) (hJsub j.2).1))
    let A : IrreducibleCharacter G → ℤ := fun χ => (mem_ZIrr_inner_int χ hΨZ).choose
    have hA : ∀ χ : IrreducibleCharacter G,
        ClassFunction.inner Ψ (χ : ClassFunction G ℂ) = (A χ : ℂ) :=
      fun χ => (mem_ZIrr_inner_int χ hΨZ).choose_spec
    have hAeq : ∀ χ : IrreducibleCharacter G, A χ = ∑ j : ↥J, n j * v j χ := by
      intro χ
      have h1 : (A χ : ℂ) = ((∑ j : ↥J, n j * v j χ : ℤ) : ℂ) := by
        rw [← hA χ, show Ψ = ∑ j : ↥J, (n j : ℂ) • delta C β₂ j.1 from rfl]
        rw [show (∑ j : ↥J, (n j : ℂ) • delta C β₂ j.1)
            = ∑ j ∈ (Finset.univ : Finset ↥J), (n j : ℂ) • delta C β₂ j.1 from rfl]
        rw [inner_sum_left, Int.cast_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [ClassFunction.inner_smul_left, hv j χ]
        push_cast; ring
      exact Int.cast_injective h1
    -- `⟨Ψ, μ'⟩ = Σ_j n_j k_j` is odd
    have hK : ClassFunction.inner Ψ μ' = ((∑ j : ↥J, n j * kF j : ℤ) : ℂ) := by
      rw [show Ψ = ∑ j : ↥J, (n j : ℂ) • delta C β₂ j.1 from rfl]
      rw [show (∑ j : ↥J, (n j : ℂ) • delta C β₂ j.1)
          = ∑ j ∈ (Finset.univ : Finset ↥J), (n j : ℂ) • delta C β₂ j.1 from rfl]
      rw [inner_sum_left, Int.cast_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ClassFunction.inner_smul_left, (hF j).2.1]
      push_cast; ring
    have hKodd : Odd (∑ j : ↥J, n j * kF j) := by
      have hz : ((∑ j : ↥J, n j * kF j : ℤ) : ZMod 2) = 1 := by
        rw [Int.cast_sum]
        have hterm : ∀ j : ↥J, ((n j * kF j : ℤ) : ZMod 2)
            = (n j : ZMod 2) * (if j = j₀ then 1 else 0) := by
          intro j
          rw [Int.cast_mul]
          congr 1
          by_cases hj : j = j₀
          · rw [if_pos hj, hj]
            exact caseB_zmod2_eq_one_of_odd ((hparity j₀).mpr rfl)
          · rw [if_neg hj]
            have hev : Even (kF j) := by
              rcases Int.even_or_odd (kF j) with he | ho
              · exact he
              · exact absurd ((hparity j).mp ho) hj
            obtain ⟨q, hq⟩ := even_iff_two_dvd.mp hev
            rw [hq]; push_cast
            have h2' : (2 : ZMod 2) = 0 := by decide
            rw [h2', zero_mul]
        have hstep1 : (∑ j : ↥J, ((n j * kF j : ℤ) : ZMod 2))
            = ∑ j : ↥J, (n j : ZMod 2) * (if j = j₀ then 1 else 0) :=
          Finset.sum_congr rfl (fun j _ => hterm j)
        have hstep2 : (∑ j : ↥J, (n j : ZMod 2) * (if j = j₀ then 1 else 0))
            = ∑ j : ↥J, (if j = j₀ then (n j : ZMod 2) else 0) :=
          Finset.sum_congr rfl (fun j _ => by by_cases hj : j = j₀ <;> simp [hj])
        rw [hstep1, hstep2, Finset.sum_ite_eq' _ j₀ (fun j => (n j : ZMod 2)),
          if_pos (Finset.mem_univ j₀)]
        exact caseB_zmod2_eq_one_of_odd hj₀odd
      exact caseB_odd_of_zmod2_eq_one hz
    -- the cross-Parseval representation of `⟨Ψ, μ'⟩`
    obtain ⟨c, hsupp, hrepr⟩ := mem_ZIrr_repr hμ'Z
    have hcross1 : ClassFunction.inner Ψ μ'
        = ∑ χ : IrreducibleCharacter G, (A χ : ℂ) * (c (χ : ClassFunction G ℂ) : ℂ) := by
      rw [OddOrder.Peterfalvi.S12.mem_ZIrr_inner_eq_sum_over_irr hμ'Z]
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      rw [hA χ, hrepr, inner_eq_coeff_of_repr χ hsupp]
    have hcross2 : (∑ χ : IrreducibleCharacter G, (A χ : ℂ) * (c (χ : ClassFunction G ℂ) : ℂ))
        = ((∑ χ : IrreducibleCharacter G, A χ * c (χ : ClassFunction G ℂ) : ℤ) : ℂ) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl (fun χ _ => by push_cast; ring)
    have hEqInt : (∑ χ : IrreducibleCharacter G, A χ * c (χ : ClassFunction G ℂ) : ℤ)
        = ∑ j : ↥J, n j * kF j := by
      have h1 : ((∑ χ : IrreducibleCharacter G, A χ * c (χ : ClassFunction G ℂ) : ℤ) : ℂ)
          = ((∑ j : ↥J, n j * kF j : ℤ) : ℂ) := by
        rw [← hcross2, ← hcross1, hK]
      exact Int.cast_injective h1
    have hOddCross : Odd (∑ χ : IrreducibleCharacter G, A χ * c (χ : ClassFunction G ℂ) : ℤ) := by
      rw [hEqInt]; exact hKodd
    obtain ⟨χ, -, hoddprod⟩ :=
      caseB_exists_odd_of_odd_sum (Finset.univ : Finset (IrreducibleCharacter G))
        (fun χ => A χ * c (χ : ClassFunction G ℂ)) hOddCross
    refine ⟨χ, ?_⟩
    rw [← hAeq χ]
    exact caseB_odd_of_odd_mul hoddprod
  -- (h5) two rows share a coordinate
  have h5 : ∃ j k : ↥J, ∃ i : IrreducibleCharacter G, j ≠ k ∧ v j i ≠ 0 ∧ v k i ≠ 0 := by
    have hnd' : ∃ χ : IrreducibleCharacter G,
        ClassFunction.inner (delta C β₂ ν₀) (χ : ClassFunction G ℂ) ≠ 0 ∧
        ClassFunction.inner (delta C β₂ μ₀) (χ : ClassFunction G ℂ) ≠ 0 := by
      by_contra hcon
      refine hAdj.2.2.2 fun χ => ?_
      by_cases h : ClassFunction.inner (delta C β₂ ν₀) (χ : ClassFunction G ℂ) = 0
      · exact Or.inl h
      · exact Or.inr (by
          by_contra h2
          exact hcon ⟨χ, h, h2⟩)
    obtain ⟨χ, h1χ, h2χ⟩ := hnd'
    exact ⟨⟨ν₀, hν₀J⟩, ⟨μ₀, hμ₀J⟩, χ,
      (fun heq => hAdj.2.2.1 (congrArg (fun z : ClassFunction ↥C.P.H0 ℂ => delta C β₂ z)
        (congrArg Subtype.val heq))),
      (by rw [hvne ⟨ν₀, hν₀J⟩ χ]; exact h1χ),
      (by rw [hvne ⟨μ₀, hμ₀J⟩ χ]; exact h2χ)⟩
  -- COMB413
  obtain ⟨j₁, j₂, j₃, hj₁₂, hj₁₃, hj₂₃, ⟨i₀, hi₀⟩, p₁, p₂, p₃, hp₁, hp₂, hp₃⟩ :=
    hComb v h1 h2orth h3 h4 h5
  -- extract the `bset'` equalities
  have hbsetχ : bset' C β₂ (i₀ : ClassFunction G ℂ) = {j₁.1, j₂.1, j₃.1} := by
    ext y
    rw [caseB_mem_bset_iff]
    constructor
    · rintro ⟨hyS, hyne⟩
      have hyJ : y ∈ J := by
        have hzS : j₁.1 ∈ bset' C β₂ (i₀ : ClassFunction G ℂ) := by
          rw [caseB_mem_bset_iff]
          exact ⟨hJsub j₁.2, (hvne j₁ i₀).mp ((hi₀ j₁).mpr (Or.inl rfl))⟩
        exact caseB_bset'_mem_J D C hc hn hβ hν₀ i₀ hzS j₁.2
          (by rw [caseB_mem_bset_iff]; exact ⟨hyS, hyne⟩)
      have hvne' : v ⟨y, hyJ⟩ i₀ ≠ 0 := (hvne ⟨y, hyJ⟩ i₀).mpr hyne
      rcases (hi₀ ⟨y, hyJ⟩).mp hvne' with h | h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (Or.inl (congrArg Subtype.val h))
      · exact Or.inr (Or.inr (congrArg Subtype.val h))
    · rintro (rfl | rfl | rfl)
      · exact ⟨hJsub j₁.2, (hvne j₁ i₀).mp ((hi₀ j₁).mpr (Or.inl rfl))⟩
      · exact ⟨hJsub j₂.2, (hvne j₂ i₀).mp ((hi₀ j₂).mpr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨hJsub j₃.2, (hvne j₃ i₀).mp ((hi₀ j₃).mpr (Or.inr (Or.inr rfl)))⟩
  have hbsetψ : ∀ (p : IrreducibleCharacter G) (j : ↥J), (∀ k : ↥J, v k p ≠ 0 ↔ k = j) →
      bset' C β₂ (p : ClassFunction G ℂ) = {j.1} := by
    intro p j hp
    ext y
    rw [caseB_mem_bset_iff]
    constructor
    · rintro ⟨hyS, hyne⟩
      have hyJ : y ∈ J := by
        have hzS : j.1 ∈ bset' C β₂ (p : ClassFunction G ℂ) := by
          rw [caseB_mem_bset_iff]
          exact ⟨hJsub j.2, (hvne j p).mp ((hp j).mpr rfl)⟩
        exact caseB_bset'_mem_J D C hc hn hβ hν₀ p hzS j.2
          (by rw [caseB_mem_bset_iff]; exact ⟨hyS, hyne⟩)
      have hvne' : v ⟨y, hyJ⟩ p ≠ 0 := (hvne ⟨y, hyJ⟩ p).mpr hyne
      have hEq : (⟨y, hyJ⟩ : ↥J) = j := (hp ⟨y, hyJ⟩).mp hvne'
      exact congrArg Subtype.val hEq
    · rintro rfl
      exact ⟨hJsub j.2, (hvne j p).mp ((hp j).mpr rfl)⟩
  -- CONG-CONTRA
  refine hCC hc hn β₂ hβ j₁.1 j₂.1 j₃.1 ?_ ?_ ?_ (i₀ : ClassFunction G ℂ)
    (p₁ : ClassFunction G ℂ) (p₂ : ClassFunction G ℂ) (p₃ : ClassFunction G ℂ)
    (Or.inl i₀.isIrreducible) (Or.inl p₁.isIrreducible) (Or.inl p₂.isIrreducible)
    (Or.inl p₃.isIrreducible) ?_ ?_ ?_ ?_
  · exact fun h => hj₁₂ (Subtype.ext h)
  · exact fun h => hj₁₃ (Subtype.ext h)
  · exact fun h => hj₂₃ (Subtype.ext h)
  · exact hbsetχ
  · exact hbsetψ p₁ j₁ hp₁
  · exact hbsetψ p₂ j₂ hp₂
  · exact hbsetψ p₃ j₃ hp₃

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem caseB {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.CaseBProp D C :=
  caseB_of_leaves D C caseBC.comb413Self (s4L41 D C) (caseBC.lemma42Self D C)
    (congContra D C)

end Work.BG
