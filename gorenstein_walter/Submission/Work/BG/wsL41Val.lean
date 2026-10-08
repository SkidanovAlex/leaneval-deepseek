/-
# Area BG: Bender–Glauberman 1981, Lemma 4.1 in the `|S| = 4` case (value form)

This is the value-form workstream (`wsL41Val`) for the §4 leaf `Work.GW2.C16.Lemma41Prop`:
for `χ ∈ ±Irr(G)` with `𝒮'(χ) ≠ ∅`,

* `|𝒮'(χ)| = 1` or `3`;
* `χ(t) = Σ_{ν ∈ 𝒮'(χ)} (χ, δ_ν) ν(1)`;
* `χ(1)` is odd,

where `δ_ν = (ν - λ₂ν)* = ind C (ν - λ₂ν)` and `𝒮'(χ) = {ν ∈ 𝒮₄(C) | (χ, δ_ν) ≠ 0}`.

The route is the paper's: `ν ∈ 𝒮'(χ)` iff `𝒮(χ) = bset C f χ` contains `ν` or `λ₂ν` (it
cannot contain both, by the coherence of `f`), so that `𝒮'(χ)` is in bijection with `𝒮(χ)`
via the `t`-even representative of the `Λ`-orbit; Lemmas 2.4, 3.3, 3.4 (proved in the
workspace) then give the count, the value at `t` and the parity of `χ(1)`.

The coherent map `f` of BG Theorem 2.3 in the `|S| = 4` case is supplied by
`Work.BG.l41_isCoherent_exists` (`Submission/Work/BG/lemma41.lean`).
-/
import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma33Leaf
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.lemma41
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.s02_sum_irr_eq_finsum_bset

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## 0. Parity bookkeeping for `AlgIntModTwo` -/

/-- A mod-`2` congruence between integers (read in the algebraic integers) has even
difference. -/
theorem ws41_even_sub_of_algIntModTwo {a b : ℤ} (h : AlgIntModTwo (a : ℂ) (b : ℂ)) :
    Even (a - b) := by
  obtain ⟨c, hc, hceq⟩ := h
  have hc2 : c = ((((a - b : ℤ) : ℚ) / 2 : ℚ) : ℂ) := by
    have h1 : c = ((a : ℂ) - (b : ℂ)) / 2 := by
      rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), mul_comm]
      exact hceq.symm
    rw [h1]
    push_cast
    ring
  obtain ⟨k, hk⟩ := (IsIntegral.exists_int_iff_exists_rat hc).mp ⟨_, hc2⟩
  have hkey : ((a - b : ℤ) : ℂ) = ((2 * k : ℤ) : ℂ) := by
    rw [hk] at hceq
    rw [show ((a - b : ℤ) : ℂ) = (a : ℂ) - (b : ℂ) by push_cast; ring,
      show ((2 * k : ℤ) : ℂ) = 2 * (k : ℂ) by push_cast; ring]
    exact hceq
  have h3 : (a - b : ℤ) = 2 * k := by exact_mod_cast hkey
  exact ⟨k, by omega⟩

/-- If `a ≡ b (mod 2)` for integers and `b` is odd, then `a` is odd. -/
theorem ws41_odd_of_algIntModTwo {a b : ℤ} (h : AlgIntModTwo (a : ℂ) (b : ℂ)) (hb : Odd b) :
    Odd a := by
  obtain ⟨k, hk⟩ := ws41_even_sub_of_algIntModTwo h
  obtain ⟨l, hl⟩ := hb
  exact ⟨k + l, by omega⟩

/-- A sum of an odd number of odd integers is odd. -/
theorem ws41_odd_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ)
    (hg : ∀ i ∈ s, Odd (g i)) (hs : Odd s.card) : Odd (∑ i ∈ s, g i) := by
  classical
  have hex : ∀ i, ∃ k : ℤ, i ∈ s → g i = 2 * k + 1 := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨k, hk⟩ := hg i hi
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hi⟩
  let k : ι → ℤ := fun i => Classical.choose (hex i)
  have hk : ∀ i ∈ s, g i = 2 * k i + 1 := fun i hi => Classical.choose_spec (hex i) hi
  have hsum : (∑ i ∈ s, g i) = 2 * (∑ i ∈ s, k i) + s.card := by
    rw [Finset.sum_congr rfl (fun i hi => hk i hi), Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum]
  obtain ⟨l, hl⟩ := hs
  exact ⟨(∑ i ∈ s, k i) + l, by omega⟩

/-! ## 1. `finsum`s over a set of irreducible characters vs. sums over the index type -/

section FinSum

variable (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

/-- A `finsum` over a set `S` of irreducible characters, with summand vanishing off `S`, is a
sum over the finite index type `Irr(H₀)`. -/
theorem ws41_sum_irr_eq_finsum [Fintype (IrreducibleCharacter ↥C.P.H0)]
    (S : Set (ClassFunction ↥C.P.H0 ℂ))
    (hS : ∀ ν : ClassFunction ↥C.P.H0 ℂ, ν ∈ S → IsIrreducibleCharacter ν)
    (F : ClassFunction ↥C.P.H0 ℂ → ℂ)
    (hF : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      (ν : ClassFunction ↥C.P.H0 ℂ) ∉ S → F (ν : ClassFunction ↥C.P.H0 ℂ) = 0) :
    (∑ ν : IrreducibleCharacter ↥C.P.H0, F (ν : ClassFunction ↥C.P.H0 ℂ)) = ∑ᶠ ν ∈ S, F ν := by
  classical
  rw [finsum_mem_def]
  have hinj : Set.InjOn
      (fun ν : IrreducibleCharacter ↥C.P.H0 => (ν : ClassFunction ↥C.P.H0 ℂ))
      ↑(Finset.univ : Finset (IrreducibleCharacter ↥C.P.H0)) :=
    fun a _ b _ h => IrreducibleCharacter.ext h
  have hsupp : Function.support (S.indicator F) ⊆
      ↑(Finset.univ.image (fun ν : IrreducibleCharacter ↥C.P.H0 =>
        (ν : ClassFunction ↥C.P.H0 ℂ))) := by
    intro ν hν
    rw [Function.mem_support] at hν
    have hmem : ν ∈ S := by
      by_contra h
      rw [Set.indicator_of_notMem h] at hν
      exact hν rfl
    exact Finset.mem_image.mpr ⟨⟨ν, hS ν hmem⟩, Finset.mem_univ _, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj]
  refine Finset.sum_congr rfl ?_
  intro ν _
  by_cases h : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ S
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, hF ν h]

/-- The indices of a set of irreducible class functions. -/
noncomputable def ws41_ifin (S : Set (ClassFunction ↥C.P.H0 ℂ)) :
    Finset (IrreducibleCharacter ↥C.P.H0) := by
  classical
  exact Finset.univ.filter (fun ν => (ν : ClassFunction ↥C.P.H0 ℂ) ∈ S)

@[simp] theorem ws41_mem_ifin {S : Set (ClassFunction ↥C.P.H0 ℂ)}
    {ν : IrreducibleCharacter ↥C.P.H0} :
    ν ∈ ws41_ifin C S ↔ (ν : ClassFunction ↥C.P.H0 ℂ) ∈ S := by
  classical simp [ws41_ifin]

/-- Cardinality of a set of irreducible class functions, as a cardinality of indices. -/
theorem ws41_ncard_eq_card [Fintype (IrreducibleCharacter ↥C.P.H0)]
    (S : Set (ClassFunction ↥C.P.H0 ℂ))
    (hS : ∀ ν : ClassFunction ↥C.P.H0 ℂ, ν ∈ S → IsIrreducibleCharacter ν) :
    S.ncard = (ws41_ifin C S).card := by
  classical
  let A : Finset (ClassFunction ↥C.P.H0 ℂ) :=
    (ws41_ifin C S).image (fun ν : IrreducibleCharacter ↥C.P.H0 => (ν : ClassFunction ↥C.P.H0 ℂ))
  have hcard : (ws41_ifin C S).card = A.card :=
    (Finset.card_image_of_injective _ (fun a b h => IrreducibleCharacter.ext h)).symm
  have hA : (A : Set (ClassFunction ↥C.P.H0 ℂ)) = S := by
    ext ν
    constructor
    · intro hν
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hν
      exact (ws41_mem_ifin C).mp hμ
    · intro hν
      exact Finset.mem_image.mpr
        ⟨⟨ν, hS ν hν⟩, (ws41_mem_ifin C).mpr hν, rfl⟩
  rw [hcard, ← Set.ncard_coe_finset, hA]

end FinSum

/-! ## 2. The `|S| = 4` situation -/

section Sec4

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

/-- The indices of `𝒮(χ) = bset C f χ`. -/
noncomputable def ws41_Tfin (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ)
    (χ : ClassFunction G ℂ) : Finset (IrreducibleCharacter ↥C.P.H0) := by
  classical
  exact Finset.univ.filter (fun ν => (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)

/-- The indices of `𝒮'(χ) = bset' C β₂ χ`. -/
noncomputable def ws41_Sfin (β₂ : quotGroup C.P →* ℂˣ) (χ : ClassFunction G ℂ) :
    Finset (IrreducibleCharacter ↥C.P.H0) := by
  classical
  exact Finset.univ.filter (fun ν => (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ)

@[simp] theorem ws41_mem_Tfin {f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ}
    {χ : ClassFunction G ℂ} {ν : IrreducibleCharacter ↥C.P.H0} :
    ν ∈ ws41_Tfin C f χ ↔ (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ := by
  rw [ws41_Tfin]; exact ws41_mem_ifin C

@[simp] theorem ws41_mem_Sfin {β₂ : quotGroup C.P →* ℂˣ} {χ : ClassFunction G ℂ}
    {ν : IrreducibleCharacter ↥C.P.H0} :
    ν ∈ ws41_Sfin C β₂ χ ↔ (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ := by
  rw [ws41_Sfin]; exact ws41_mem_ifin C

variable [Fintype (IrreducibleCharacter ↥C.P.H0)]

/-- `𝒮(χ)` has the cardinality of the corresponding finset of indices. -/
theorem ws41_ncard_bset (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ)
    (χ : ClassFunction G ℂ) :
    (bset C f χ).ncard = (ws41_Tfin C f χ).card :=
  ws41_ncard_eq_card C (bset C f χ) (fun _ hν => hν.1)

/-- `𝒮'(χ)` has the cardinality of the corresponding finset of indices. -/
theorem ws41_ncard_bset' (β₂ : quotGroup C.P →* ℂˣ) (χ : ClassFunction G ℂ) :
    (bset' C β₂ χ).ncard = (ws41_Sfin C β₂ χ).card :=
  ws41_ncard_eq_card C (bset' C β₂ χ) (fun _ hν => hν.1.1)

/-! ## 3. The `t`-even representative of a `Λ`-orbit -/

section Tv

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
variable (β₂ : quotGroup C.P →* ℂˣ)

/-- `λ₂` takes the value `1` at the identity. -/
theorem ws41_lamCF_apply_one : (lamCF C β₂ : ClassFunction ↥C.P.H0 ℂ) 1 = 1 := by
  simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]

/-- The `t`-even member of the `Λ`-orbit of `ν`: `ν` if `ν(t) = ν(1)`, else `λ₂ν`. -/
noncomputable def ws41_tv (ν : ClassFunction ↥C.P.H0 ℂ) : ClassFunction ↥C.P.H0 ℂ :=
  if ν C.t = ν 1 then ν else lamCF C β₂ * ν

theorem ws41_tv_eq_self {ν : ClassFunction ↥C.P.H0 ℂ} (h : ν C.t = ν 1) :
    ws41_tv C β₂ ν = ν := by rw [ws41_tv, if_pos h]

theorem ws41_tv_eq_mul {ν : ClassFunction ↥C.P.H0 ℂ} (h : ν C.t ≠ ν 1) :
    ws41_tv C β₂ ν = lamCF C β₂ * ν := by rw [ws41_tv, if_neg h]

theorem ws41_tv_or (ν : ClassFunction ↥C.P.H0 ℂ) :
    ws41_tv C β₂ ν = ν ∨ ws41_tv C β₂ ν = lamCF C β₂ * ν := by
  by_cases h : ν C.t = ν 1
  · exact Or.inl (ws41_tv_eq_self C β₂ h)
  · exact Or.inr (ws41_tv_eq_mul C β₂ h)

theorem ws41_tv_irr {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    IsIrreducibleCharacter (ws41_tv C β₂ ν) := by
  rcases ws41_tv_or C β₂ ν with h | h
  · rw [h]; exact hν
  · rw [h]; exact lam_two_mul_irr C hν

theorem ws41_tv_apply_one (ν : ClassFunction ↥C.P.H0 ℂ) :
    ws41_tv C β₂ ν 1 = ν 1 := by
  rcases ws41_tv_or C β₂ ν with h | h
  · rw [h]
  · rw [h, ClassFunction.mul_apply, ws41_lamCF_apply_one, one_mul]

theorem ws41_tv_lamOrbit' (ν : ClassFunction ↥C.P.H0 ℂ) : LamEquiv C ν (ws41_tv C β₂ ν) := by
  rcases ws41_tv_or C β₂ ν with h | h
  · refine ⟨1, ?_⟩
    rw [h, lamCF_one_eq]
    exact (one_mul_cf ν).symm
  · exact ⟨β₂, by rw [h]⟩

theorem ws41_tv_lamOrbit (ν : ClassFunction ↥C.P.H0 ℂ) : LamEquiv C (ws41_tv C β₂ ν) ν :=
  s02c_LamEquiv_symm C (ws41_tv_lamOrbit' C β₂ ν)

theorem ws41_tv_apply_t {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) :
    ws41_tv C β₂ ν C.t = ws41_tv C β₂ ν 1 := by
  by_cases h : ν C.t = ν 1
  · rw [ws41_tv_eq_self C β₂ h, h]
  · rw [ws41_tv_apply_one, ws41_tv_eq_mul C β₂ h, lam_two_mul_apply_t C h2 hβ ν]
    rcases t_val_or C hν with ht | ht
    · exact absurd ht h
    · rw [ht]; ring

theorem ws41_tv_mem_S4Index {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    (hfix : sconj C ν = ν) (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) :
    ws41_tv C β₂ ν ∈ S4Index C := by
  refine ⟨ws41_tv_irr C β₂ hν, ?_, ws41_tv_apply_t C β₂ hν h2 hβ⟩
  rcases ws41_tv_or C β₂ ν with h | h
  · rw [h]; exact hfix
  · rw [h, sconj_lam_two_mul C h2 hβ, hfix]

/-- The `t`-even member of the `Λ`-orbit, on the index type. -/
noncomputable def ws41_tvI [Fintype (IrreducibleCharacter ↥C.P.H0)]
    (ν : IrreducibleCharacter ↥C.P.H0) : IrreducibleCharacter ↥C.P.H0 :=
  if ((ν : ClassFunction ↥C.P.H0 ℂ) C.t = (ν : ClassFunction ↥C.P.H0 ℂ) 1) then ν
  else ⟨lamCF C β₂ * (ν : ClassFunction ↥C.P.H0 ℂ), lam_two_mul_irr C ν.2⟩

theorem ws41_tvI_coe [Fintype (IrreducibleCharacter ↥C.P.H0)]
    (ν : IrreducibleCharacter ↥C.P.H0) :
    (ws41_tvI C β₂ ν : ClassFunction ↥C.P.H0 ℂ) =
      ws41_tv C β₂ (ν : ClassFunction ↥C.P.H0 ℂ) := by
  rw [ws41_tvI]
  by_cases h : ((ν : ClassFunction ↥C.P.H0 ℂ) C.t = (ν : ClassFunction ↥C.P.H0 ℂ) 1)
  · rw [if_pos h, ws41_tv_eq_self C β₂ h]
  · rw [if_neg h, ws41_tv_eq_mul C β₂ h]

end Tv


/-! ## 8. Lemma 3.4 in the case `|S| = 4` (the exceptional configuration is impossible) -/

section Lemma34

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
variable [Fintype (IrreducibleCharacter ↥C.P.H0)]

/-- A norm-one element of `ℤ[Irr G]` meeting a signed irreducible is `±` that character. -/
theorem ws41_eq_pm_of_inner_ne_zero {φ χ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hnorm : ClassFunction.inner φ φ = 1) (hχ : IsPmIrr χ)
    (h : ClassFunction.inner χ φ ≠ 0) : φ = χ ∨ φ = -χ := by
  obtain ⟨ε, ψ, hε, hφeq⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hφ hnorm
  have hinner : ClassFunction.inner χ (ψ : ClassFunction G ℂ) ≠ 0 := by
    rcases hε with rfl | rfl
    · rw [one_smul] at hφeq; rw [← hφeq]; exact h
    · rw [neg_smul, one_smul] at hφeq
      have h' : ClassFunction.inner χ (-(ψ : ClassFunction G ℂ)) ≠ 0 := by
        rw [← hφeq]; exact h
      rw [ClassFunction.inner_neg_right] at h'
      exact neg_ne_zero.mp h'
  rcases hχ with hχi | hχi
  · have hχψ : χ = (ψ : ClassFunction G ℂ) := by
      by_contra hc
      have h0 : ClassFunction.inner χ (ψ : ClassFunction G ℂ) = 0 := by
        rw [irreducibleCharacter_inner_eq_ite ⟨χ, hχi⟩ ψ]
        exact ite_eq_right (fun hh => hc (by simpa using congrArg Subtype.val hh))
      exact hinner h0
    rcases hε with rfl | rfl
    · left; rw [hφeq, one_smul]; exact hχψ.symm
    · right; rw [hφeq, neg_smul, one_smul, ← hχψ]
  · have hnegψ : -χ = (ψ : ClassFunction G ℂ) := by
      by_contra hc
      have h0 : ClassFunction.inner (-χ) (ψ : ClassFunction G ℂ) = 0 := by
        rw [irreducibleCharacter_inner_eq_ite ⟨-χ, hχi⟩ ψ]
        exact ite_eq_right (fun hh => hc (by simpa using congrArg Subtype.val hh))
      have hh := ClassFunction.inner_neg_left (G := G) χ (ψ : ClassFunction G ℂ)
      rw [h0] at hh
      exact hinner (neg_eq_zero.mp hh.symm)
    rcases hε with rfl | rfl
    · right; rw [hφeq, one_smul, ← hnegψ]
    · left
      have h2 : χ = -(ψ : ClassFunction G ℂ) := by
        have := congrArg (fun z : ClassFunction G ℂ => -z) hnegψ
        simpa using this
      rw [hφeq, neg_smul, one_smul, ← h2]

/-- **Lemma 3.4 in the case `|S| = 4`.**  If `ν ∈ 𝒮(χ)` is not `s`-fixed and
`|Λν| = D.n`, then `𝒮(χ) = {ν, ν^s}`.  (In this case `|Λν| = D.n = 2`, so the exceptional
configuration `|Λν| = 4 ∧ (Λν)^s = Λν` of the full Lemma 3.4 cannot occur, and the argument
of `Work.BG.lemma34Leaf` goes through without `Work.BG.lemma34Exc`.) -/
theorem ws41_lemma34 (hDC : Compat D C) (hS3 : Sec3Hyp D) (hn : D.n = 2)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (hlam : (lamOrbit C ν).ncard = D.n) : bset C f χ = {ν, sconj C ν} := by
  obtain ⟨hνirr, hνne0⟩ := hν
  have hkey : ν ∈ orbitKey C ν := Or.inl (s02c_LamEquiv_refl C ν)
  have hG := (hf.1 ν hνirr) ν hkey ν hkey hνirr hνirr
  obtain ⟨hZIfν, hsconjf, hnormf, -, -, hvi⟩ := hG
  have hnormf1 : ClassFunction.inner (f ν) (f ν) = 1 := by rw [hnormf]; simp [hne]
  obtain ⟨ε, ψ, hε, hfeq⟩ :=
    exists_zsmul_irreducibleCharacter_of_inner_self_one hZIfν hnormf1
  have hpmfν : IsPmIrr (f ν) := by
    rcases hε with rfl | rfl
    · left; rw [hfeq, one_smul]; exact ψ.2
    · right
      have h2 : -(f ν) = (ψ : ClassFunction G ℂ) := by rw [hfeq]; simp
      rw [h2]; exact ψ.2
  have hχeq : χ = f ν ∨ χ = - f ν := by
    rcases ws41_eq_pm_of_inner_ne_zero hZIfν hnormf1 hχ hνne0 with h | h
    · exact Or.inl h.symm
    · refine Or.inr ?_
      have h2 : - f ν = χ := by rw [h]; simp
      exact h2.symm
  have hbset_eq : bset C f (f ν) = bset C f χ := by
    rcases hχeq with h | h
    · rw [h]
    · rw [h]
      ext η
      simp only [bset, Set.mem_ofPred_eq]
      rw [ClassFunction.inner_neg_left]
      simp
  have hνs_mem : sconj C ν ∈ bset C f χ := by
    refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hνirr, ?_⟩
    rw [hsconjf]; exact hνne0
  have hsub2 : ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro η hη
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl
    · exact ⟨hνirr, hνne0⟩
    · exact hνs_mem
  -- the exceptional configuration is impossible when `|Λν| = 2`
  have hexc : ¬((lamOrbit C ν).ncard = 4 ∧ sconj C '' lamOrbit C ν = lamOrbit C ν) := by
    intro hcon
    rw [hlam, hn] at hcon
    exact absurd hcon.1 (by norm_num)
  -- `𝒮(χ) = {ν, ν^s}`
  have hcard : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  ext ξ
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hξ
    by_contra hnot
    have hξν : ξ ≠ ν := fun h => hnot (Or.inl h)
    have hξνs : ξ ≠ sconj C ν := fun h => hnot (Or.inr h)
    obtain ⟨hξirr, hξne0⟩ := hξ
    have hsub : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
      intro η hη
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hη
      rcases hη with rfl | rfl | rfl
      · exact ⟨hνirr, hνne0⟩
      · exact hνs_mem
      · exact ⟨hξirr, hξne0⟩
    have hnot1 : ν ∉ ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      intro hmem
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · exact hne h.symm
      · exact hξν h.symm
    have hnot2 : sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      intro hmem
      rw [Set.mem_singleton_iff] at hmem
      exact hξνs hmem.symm
    have h3 : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (s := ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
            (a := ν) hnot1 (Set.toFinite _),
          Set.ncard_insert_of_notMem (s := ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
            (a := sconj C ν) hnot2 (Set.toFinite _),
          Set.ncard_singleton]
    have heq : bset C f χ = {ν, sconj C ν, ξ} :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [h3]; exact hcard) hfin).symm
    -- the value at `t` from coherence
    have hval : f ν (C.t : G) = 2 * ν C.t := hvi hne hexc
    have hbsetν : bset C f (f ν) = {ν, sconj C ν, ξ} := by rw [hbset_eq]; exact heq
    have hT := (lemma24 C f hf (f ν) hpmfν).2.1 C.t C.t_not_mem_U
    have hsum : (∑ᶠ η ∈ bset C f (f ν), ClassFunction.inner (f ν) (f η) * η C.t)
        = 2 * ν C.t + ClassFunction.inner (f ν) (f ξ) * ξ C.t := by
      rw [hbsetν,
        finsum_mem_insert (f := fun η => ClassFunction.inner (f ν) (f η) * η C.t)
          (a := ν) (s := ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
          hnot1 (Set.toFinite _),
        finsum_mem_insert (f := fun η => ClassFunction.inner (f ν) (f η) * η C.t)
          (a := sconj C ν) (s := ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) hnot2 (Set.toFinite _),
        finsum_mem_singleton,
        hsconjf, hnormf1, sconj_apply_t]
      ring
    rw [hsum] at hT
    rw [hval] at hT
    have hξmemν : ξ ∈ bset C f (f ν) := by
      rw [hbsetν]
      exact Set.mem_insert_of_mem ν (Set.mem_insert_of_mem (sconj C ν) (Set.mem_singleton ξ))
    have hzero : ClassFunction.inner (f ν) (f ξ) * ξ C.t = 0 := by
      have h1 : 2 * ν C.t + ClassFunction.inner (f ν) (f ξ) * ξ C.t = 2 * ν C.t + 0 := by
        rw [add_zero]; exact hT.symm
      exact add_left_cancel h1
    exact mul_ne_zero hξmemν.2 (value_t_ne_zero C ξ hξirr) hzero
  · rintro (rfl | rfl)
    · exact ⟨hνirr, hνne0⟩
    · exact hνs_mem

end Lemma34

/-! ## 4. The main assembly -/

section Assembly

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
variable [Fintype (IrreducibleCharacter ↥C.P.H0)]
variable (β₂ : quotGroup C.P →* ℂˣ)

/-- `δ_ν = ν̃ - (λ₂ν)~`: coherence identifies `δ_ν` with the difference of the coherent
extensions (BG Theorem 2.3 (iii)). -/
theorem ws41_delta_eq (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    {ξ : ClassFunction ↥C.P.H0 ℂ} (hξ : IsIrreducibleCharacter ξ) :
    delta C β₂ ξ = f ξ - f (lamCF C β₂ * ξ) := by
  have hkey := (hf.1 ξ hξ) ξ (Or.inl (s02c_LamEquiv_refl C ξ))
    (lamCF C β₂ * ξ) (Or.inl ⟨β₂, rfl⟩) hξ (lam_two_mul_irr C hξ)
  exact hkey.2.2.2.1 ⟨β₂, rfl⟩

/-- Under `𝒮'(χ) ≠ ∅`, every element of `𝒮(χ)` is `s`-fixed (Lemma 3.4 plus coherence). -/
theorem ws41_all_fixed (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (hne : (bset' C β₂ χ).Nonempty) :
    ∀ ν ∈ bset C f χ, sconj C ν = ν := by
  have h2 := quotGroup_card_two D C hc hn
  have hS3 : Sec3Hyp D := l41_sec3Hyp D hn
  intro ν hν
  by_contra hfix
  have hTeq := ws41_lemma34 D C hc hS3 hn f hf χ hχ hν hfix
    (by rw [lamOrbit_ncard_eq_two C h2 hβ hν.1, hn])
  obtain ⟨ξ, hξ⟩ := hne
  have hξirr : IsIrreducibleCharacter ξ := hξ.1.1
  have hξfix : sconj C ξ = ξ := hξ.1.2.1
  have hξne : ClassFunction.inner χ (delta C β₂ ξ) ≠ 0 := hξ.2
  have hξnotmem : ξ ∉ bset C f χ := by
    intro hmem
    rw [hTeq] at hmem
    rcases hmem with h | h
    · exact hfix (by rw [← h]; exact hξfix)
    · rw [h] at hξfix
      rw [sconj_sconj] at hξfix
      exact hfix hξfix.symm
  have hlamfix : sconj C (lamCF C β₂ * ξ) = lamCF C β₂ * ξ := by
    rw [sconj_lam_two_mul C h2 hβ, hξfix]
  have hlamnotmem : lamCF C β₂ * ξ ∉ bset C f χ := by
    intro hmem
    rw [hTeq] at hmem
    rcases hmem with h' | h'
    · exact hfix (by rw [← h']; exact hlamfix)
    · rw [h'] at hlamfix
      rw [sconj_sconj] at hlamfix
      exact hfix hlamfix.symm
  have hz1 : ClassFunction.inner χ (f ξ) = 0 := by
    by_contra hc0
    exact hξnotmem ⟨hξirr, hc0⟩
  have hz2 : ClassFunction.inner χ (f (lamCF C β₂ * ξ)) = 0 := by
    by_contra hc0
    exact hlamnotmem ⟨lam_two_mul_irr C hξirr, hc0⟩
  have hd := ws41_delta_eq C β₂ f hf hξirr
  exact hξne (by rw [hd, ClassFunction.inner_sub_right, hz1, hz2, sub_zero])

/-- If all of `𝒮(χ)` is `s`-fixed, then `λ₂ν ∉ 𝒮(χ)` for `ν ∈ 𝒮(χ)`. -/
theorem ws41_lam_not_mem (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (hall : ∀ ν ∈ bset C f χ, sconj C ν = ν)
    {ξ : ClassFunction ↥C.P.H0 ℂ} (hξ : ξ ∈ bset C f χ) : lamCF C β₂ * ξ ∉ bset C f χ := by
  intro hmem
  have h2 := quotGroup_card_two D C hc hn
  have hne := lam_two_mul_ne_self C h2 hβ hξ.1
  have h := (bset_orbit_struct C f hf χ hχ).2 ξ hξ (lamCF C β₂ * ξ) hmem ⟨β₂, rfl⟩ hne
  rw [hall ξ hξ] at h
  exact hne h

/-- The `t`-even representative of the orbit of `ξ ∈ 𝒮(χ)` lies in `𝒮'(χ)`. -/
theorem ws41_tv_mem_bset' (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (hall : ∀ ν ∈ bset C f χ, sconj C ν = ν)
    {ξ : ClassFunction ↥C.P.H0 ℂ} (hξ : ξ ∈ bset C f χ) :
    ws41_tv C β₂ ξ ∈ bset' C β₂ χ := by
  have h2 := quotGroup_card_two D C hc hn
  have hirr : IsIrreducibleCharacter ξ := hξ.1
  have hfix : sconj C ξ = ξ := hall ξ hξ
  have hS4 := ws41_tv_mem_S4Index C β₂ hirr hfix h2 hβ
  have hmul : ∀ μ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ →
      μ ∈ bset C f χ → ClassFunction.inner χ (f μ) ≠ 0 := fun μ hμ hmem => hmem.2
  have hnot : ∀ μ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ →
      μ ∉ bset C f χ → ClassFunction.inner χ (f μ) = 0 := by
    intro μ hμ hmem
    by_contra hc0
    exact hmem ⟨hμ, hc0⟩
  rcases ws41_tv_or C β₂ ξ with h | h
  · have hz : ClassFunction.inner χ (f (lamCF C β₂ * ξ)) = 0 :=
      hnot _ (lam_two_mul_irr C hirr)
        (ws41_lam_not_mem D C β₂ hc hn hβ f hf χ hχ hall hξ)
    refine ⟨hS4, ?_⟩
    rw [h, ws41_delta_eq C β₂ f hf hirr, ClassFunction.inner_sub_right, hz, sub_zero]
    exact hξ.2
  · have hz : ClassFunction.inner χ (f (lamCF C β₂ * ξ)) = 0 :=
      hnot _ (lam_two_mul_irr C hirr)
        (ws41_lam_not_mem D C β₂ hc hn hβ f hf χ hχ hall hξ)
    have hcancel : lamCF C β₂ * (lamCF C β₂ * ξ) = ξ := by
      rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
    refine ⟨hS4, ?_⟩
    rw [h, ws41_delta_eq C β₂ f hf (lam_two_mul_irr C hirr), hcancel,
      ClassFunction.inner_sub_right, hz, zero_sub]
    exact neg_ne_zero.mpr hξ.2

/-- Term matching: the contribution of `ξ ∈ 𝒮(χ)` in Lemma 2.4 equals the contribution of its
`t`-even orbit representative in Lemma 4.1 (ii). -/
theorem ws41_term (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (hall : ∀ ν ∈ bset C f χ, sconj C ν = ν)
    {ξ : ClassFunction ↥C.P.H0 ℂ} (hξ : ξ ∈ bset C f χ) :
    ClassFunction.inner χ (f ξ) * (ξ C.t)
      = ClassFunction.inner χ (delta C β₂ (ws41_tv C β₂ ξ)) * ((ws41_tv C β₂ ξ) 1) := by
  have h2 := quotGroup_card_two D C hc hn
  have hirr : IsIrreducibleCharacter ξ := hξ.1
  have hz : ClassFunction.inner χ (f (lamCF C β₂ * ξ)) = 0 := by
    by_contra hc0
    exact ws41_lam_not_mem D C β₂ hc hn hβ f hf χ hχ hall hξ
      ⟨lam_two_mul_irr C hirr, hc0⟩
  rcases ws41_tv_or C β₂ ξ with h | h
  · have ht : ξ C.t = ξ 1 := by
      by_contra hne
      rw [ws41_tv_eq_mul C β₂ hne] at h
      exact lam_two_mul_ne_self C h2 hβ hirr h
    rw [h, ws41_delta_eq C β₂ f hf hirr, ClassFunction.inner_sub_right, hz, sub_zero, ht]
  · rw [h, ws41_delta_eq C β₂ f hf (lam_two_mul_irr C hirr)]
    have hcancel : lamCF C β₂ * (lamCF C β₂ * ξ) = ξ := by
      rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
    have h1 : (lamCF C β₂ * ξ) 1 = ξ 1 := by
      rw [ClassFunction.mul_apply, ws41_lamCF_apply_one, one_mul]
    have hξt : ξ C.t = -(ξ 1) := by
      rcases t_val_or C hirr with ht | ht
      · exfalso
        rw [ws41_tv_eq_self C β₂ ht] at h
        exact lam_two_mul_ne_self C h2 hβ hirr h.symm
      · exact ht
    rw [hcancel, ClassFunction.inner_sub_right, hz, zero_sub, h1, hξt]
    ring

end Assembly


/-! ## 5. `finsum`s over `𝒮(χ)` and `𝒮'(χ)` as sums over the index finsets -/

section FinSums

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
variable [Fintype (IrreducibleCharacter ↥C.P.H0)]

/-- A `finsum` over `𝒮(χ)` is a sum over the index finset. -/
theorem ws41_finsum_bset (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ)
    (χ : ClassFunction G ℂ) (F : ClassFunction ↥C.P.H0 ℂ → ℂ) :
    (∑ᶠ ν ∈ bset C f χ, F ν)
      = (ws41_Tfin C f χ).sum (fun ν : IrreducibleCharacter ↥C.P.H0 => F ν.toClassFunction) := by
  classical
  rw [finsum_mem_def]
  have hinj : Set.InjOn (fun ν : IrreducibleCharacter ↥C.P.H0 => (ν : ClassFunction ↥C.P.H0 ℂ))
      ↑(Finset.univ : Finset (IrreducibleCharacter ↥C.P.H0)) :=
    fun a _ b _ h => IrreducibleCharacter.ext h
  have hsupp : Function.support ((bset C f χ).indicator F) ⊆
      ↑(Finset.univ.image (fun ν : IrreducibleCharacter ↥C.P.H0 =>
        (ν : ClassFunction ↥C.P.H0 ℂ))) := by
    intro ν hν
    rw [Function.mem_support] at hν
    have hmem : ν ∈ bset C f χ := by
      by_contra h
      rw [Set.indicator_of_notMem h] at hν
      exact hν rfl
    exact Finset.mem_image.mpr ⟨⟨ν, hmem.1⟩, Finset.mem_univ _, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj, ws41_Tfin,
    Finset.sum_filter]
  simp only [Set.indicator_apply]
  exact Finset.sum_congr (by ext x; simp) (fun x _ => rfl)

/-- A `finsum` over `𝒮'(χ)` is a sum over the index finset. -/
theorem ws41_finsum_bset' (β₂ : quotGroup C.P →* ℂˣ) (χ : ClassFunction G ℂ)
    (F : ClassFunction ↥C.P.H0 ℂ → ℂ) :
    (∑ᶠ ν ∈ bset' C β₂ χ, F ν)
      = (ws41_Sfin C β₂ χ).sum (fun ν : IrreducibleCharacter ↥C.P.H0 => F ν.toClassFunction) := by
  classical
  rw [finsum_mem_def]
  have hinj : Set.InjOn (fun ν : IrreducibleCharacter ↥C.P.H0 => (ν : ClassFunction ↥C.P.H0 ℂ))
      ↑(Finset.univ : Finset (IrreducibleCharacter ↥C.P.H0)) :=
    fun a _ b _ h => IrreducibleCharacter.ext h
  have hsupp : Function.support ((bset' C β₂ χ).indicator F) ⊆
      ↑(Finset.univ.image (fun ν : IrreducibleCharacter ↥C.P.H0 =>
        (ν : ClassFunction ↥C.P.H0 ℂ))) := by
    intro ν hν
    rw [Function.mem_support] at hν
    have hmem : ν ∈ bset' C β₂ χ := by
      by_contra h
      rw [Set.indicator_of_notMem h] at hν
      exact hν rfl
    exact Finset.mem_image.mpr ⟨⟨ν, hmem.1.1⟩, Finset.mem_univ _, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj, ws41_Sfin,
    Finset.sum_filter]
  simp only [Set.indicator_apply]
  exact Finset.sum_congr (by ext x; simp) (fun x _ => rfl)

end FinSums

/-! ## 6. The bijection `𝒮(χ) ≃ 𝒮'(χ)` through the `t`-even orbit representative -/

section Bij

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
variable [Fintype (IrreducibleCharacter ↥C.P.H0)]
variable (β₂ : quotGroup C.P →* ℂˣ)

theorem ws41_tvI_mapsTo (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (hne : (bset' C β₂ χ).Nonempty) :
    Set.MapsTo (ws41_tvI C β₂) ↑(ws41_Tfin C f χ) ↑(ws41_Sfin C β₂ χ) := by
  have hall := ws41_all_fixed D C β₂ hc hn hβ f hf χ hχ hne
  intro a ha
  rw [Finset.mem_coe] at ha
  rw [Finset.mem_coe, ws41_mem_Sfin C]
  rw [ws41_tvI_coe C β₂ a]
  exact ws41_tv_mem_bset' D C β₂ hc hn hβ f hf χ hχ hall ((ws41_mem_Tfin C).mp ha)

theorem ws41_tvI_injOn (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (hne : (bset' C β₂ χ).Nonempty) :
    (↑(ws41_Tfin C f χ) : Set (IrreducibleCharacter ↥C.P.H0)).InjOn (ws41_tvI C β₂) := by
  have hall := ws41_all_fixed D C β₂ hc hn hβ f hf χ hχ hne
  intro a ha b hb hab
  have hmem_a : (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ := (ws41_mem_Tfin C).mp ha
  have hmem_b : (b : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ := (ws41_mem_Tfin C).mp hb
  have hcoe : ws41_tv C β₂ (a : ClassFunction ↥C.P.H0 ℂ) =
      ws41_tv C β₂ (b : ClassFunction ↥C.P.H0 ℂ) := by
    rw [← ws41_tvI_coe C β₂ a, ← ws41_tvI_coe C β₂ b, hab]
  have hL : LamEquiv C (a : ClassFunction ↥C.P.H0 ℂ) (b : ClassFunction ↥C.P.H0 ℂ) :=
    s02c_LamEquiv_trans C (ws41_tv_lamOrbit' C β₂ (a : ClassFunction ↥C.P.H0 ℂ))
      (by rw [hcoe]; exact s02c_LamEquiv_symm C (ws41_tv_lamOrbit' C β₂ (b : ClassFunction ↥C.P.H0 ℂ)))
  by_cases hEq : (b : ClassFunction ↥C.P.H0 ℂ) = (a : ClassFunction ↥C.P.H0 ℂ)
  · exact IrreducibleCharacter.ext hEq.symm
  · have hconj := (bset_orbit_struct C f hf χ hχ).2
      (a : ClassFunction ↥C.P.H0 ℂ) hmem_a (b : ClassFunction ↥C.P.H0 ℂ) hmem_b hL hEq
    rw [hall (a : ClassFunction ↥C.P.H0 ℂ) hmem_a] at hconj
    exact absurd hconj hEq

theorem ws41_tvI_surjOn (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (hne : (bset' C β₂ χ).Nonempty) :
    (↑(ws41_Tfin C f χ) : Set (IrreducibleCharacter ↥C.P.H0)).SurjOn (ws41_tvI C β₂)
      ↑(ws41_Sfin C β₂ χ) := by
  have hall := ws41_all_fixed D C β₂ hc hn hβ f hf χ hχ hne
  have h2 := quotGroup_card_two D C hc hn
  intro b hb
  have hb' : (b : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ := (ws41_mem_Sfin C).mp hb
  have hS4 : (b : ClassFunction ↥C.P.H0 ℂ) ∈ S4Index C := hb'.1
  have hirr : IsIrreducibleCharacter (b : ClassFunction ↥C.P.H0 ℂ) := hS4.1
  have ht : (b : ClassFunction ↥C.P.H0 ℂ) C.t = (b : ClassFunction ↥C.P.H0 ℂ) 1 := hS4.2.2
  have hd := ws41_delta_eq C β₂ f hf hirr
  have hex : (b : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ ∨
      lamCF C β₂ * (b : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ := by
    by_contra hcon
    rw [not_or] at hcon
    have h1 : ClassFunction.inner χ (f (b : ClassFunction ↥C.P.H0 ℂ)) = 0 := by
      by_contra hc0
      exact hcon.1 ⟨hirr, hc0⟩
    have h2' : ClassFunction.inner χ (f (lamCF C β₂ * (b : ClassFunction ↥C.P.H0 ℂ))) = 0 := by
      by_contra hc0
      exact hcon.2 ⟨lam_two_mul_irr C hirr, hc0⟩
    exact hb'.2 (by rw [hd, ClassFunction.inner_sub_right, h1, h2', sub_zero])
  rcases hex with hmem | hmem
  · refine ⟨b, (ws41_mem_Tfin C).mpr hmem, ?_⟩
    exact IrreducibleCharacter.ext (by rw [ws41_tvI_coe C β₂ b, ws41_tv_eq_self C β₂ ht])
  · refine ⟨⟨lamCF C β₂ * (b : ClassFunction ↥C.P.H0 ℂ), lam_two_mul_irr C hirr⟩,
      (ws41_mem_Tfin C).mpr hmem, ?_⟩
    refine IrreducibleCharacter.ext ?_
    rw [ws41_tvI_coe C β₂ ⟨lamCF C β₂ * (b : ClassFunction ↥C.P.H0 ℂ), lam_two_mul_irr C hirr⟩]
    have hne' : (lamCF C β₂ * (b : ClassFunction ↥C.P.H0 ℂ)) C.t ≠
        (lamCF C β₂ * (b : ClassFunction ↥C.P.H0 ℂ)) 1 := by
      rw [lam_two_mul_apply_t C h2 hβ, ClassFunction.mul_apply, ws41_lamCF_apply_one, one_mul, ht]
      intro hcon
      have hsum : ((b : ClassFunction ↥C.P.H0 ℂ) 1) + ((b : ClassFunction ↥C.P.H0 ℂ) 1) = 0 :=
        neg_eq_iff_add_eq_zero.mp hcon
      have htwo : (2 : ℂ) * ((b : ClassFunction ↥C.P.H0 ℂ) 1) = 0 := by
        rw [two_mul]; exact hsum
      exact irr_apply_one_ne_zero C hirr ((mul_eq_zero.mp htwo).resolve_left (by norm_num))
    rw [ws41_tv_eq_mul C β₂ hne', ← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]

/-- `𝒮'(χ)` and `𝒮(χ)` have the same cardinality. -/
theorem ws41_ncard_eq (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (hne : (bset' C β₂ χ).Nonempty) :
    (bset' C β₂ χ).ncard = (bset C f χ).ncard := by
  have hbij : (ws41_Tfin C f χ).card = (ws41_Sfin C β₂ χ).card :=
    Finset.card_nbij (ws41_tvI C β₂) (ws41_tvI_mapsTo D C β₂ hc hn hβ f hf χ hχ hne)
      (ws41_tvI_injOn D C β₂ hc hn hβ f hf χ hχ hne)
      (ws41_tvI_surjOn D C β₂ hc hn hβ f hf χ hχ hne)
  rw [ws41_ncard_bset' C β₂ χ, ws41_ncard_bset C f χ, hbij]

end Bij


/-! ## 7. Lemma 4.1 (i), (ii), (iv) -/

section Main

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
variable [Fintype (IrreducibleCharacter ↥C.P.H0)]
variable (β₂ : quotGroup C.P →* ℂˣ)

/-- Lemma 4.1 (i): `|𝒮'(χ)| = 1` or `3`. -/
theorem ws41_part_i (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (hne : (bset' C β₂ χ).Nonempty) :
    (bset' C β₂ χ).ncard = 1 ∨ (bset' C β₂ χ).ncard = 3 := by
  classical
  have h2 := quotGroup_card_two D C hc hn
  have hS3 : Sec3Hyp D := l41_sec3Hyp D hn
  have hall := ws41_all_fixed D C β₂ hc hn hβ f hf χ hχ hne
  have hcard := ws41_ncard_eq D C β₂ hc hn hβ f hf χ hχ hne
  have hle3 : (bset C f χ).ncard ≤ 3 := thm32 D C hc hS3 f hf χ hχ
  have hfin : (bset' C β₂ χ).Finite :=
    (Set.finite_univ.image (fun ν : IrreducibleCharacter ↥C.P.H0 =>
      (ν : ClassFunction ↥C.P.H0 ℂ))).subset (fun ν hν => ⟨⟨ν, hν.1.1⟩, Set.mem_univ _, rfl⟩)
  have hpos : 0 < (bset C f χ).ncard := by
    rw [← hcard]
    exact (Set.ncard_pos hfin).mpr hne
  have hne2 : (bset C f χ).ncard ≠ 2 := by
    intro h2n
    have hTcard : (ws41_Tfin C f χ).card = 2 := by
      rw [← ws41_ncard_bset C f χ]; exact h2n
    obtain ⟨a, b, hab, hTeq⟩ := Finset.card_eq_two.mp hTcard
    have hamem : (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ :=
      (ws41_mem_Tfin C).mp (by rw [hTeq]; simp)
    have hbmem : (b : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ :=
      (ws41_mem_Tfin C).mp (by rw [hTeq]; simp)
    have h33 := lemma33Leaf D C hc hS3 f hf χ hχ (a : ClassFunction ↥C.P.H0 ℂ) hamem
      (b : ClassFunction ↥C.P.H0 ℂ) hbmem (fun h => hab (IrreducibleCharacter.ext h))
      (hall _ hamem) (hall _ hbmem)
      (by rw [lamOrbit_ncard_eq_two C h2 hβ hamem.1, hn])
      (by rw [lamOrbit_ncard_eq_two C h2 hβ hbmem.1, hn])
    rw [h33.2.1] at h2n
    exact absurd h2n (by norm_num)
  have hmain : (bset C f χ).ncard = 1 ∨ (bset C f χ).ncard = 3 := by omega
  rw [hcard]
  exact hmain

/-- Lemma 4.1 (ii): the value of `χ` at `t` as a signed sum of degrees. -/
theorem ws41_part_ii (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (hne : (bset' C β₂ χ).Nonempty) :
    χ (C.t : G) = ∑ᶠ ν ∈ bset' C β₂ χ, ClassFunction.inner χ (delta C β₂ ν) * ν 1 := by
  have hall := ws41_all_fixed D C β₂ hc hn hβ f hf χ hχ hne
  rw [(lemma24 C f hf χ hχ).2.1 C.t C.t_not_mem_U]
  rw [ws41_finsum_bset C f χ (fun ξ => ClassFunction.inner χ (f ξ) * ξ C.t)]
  rw [ws41_finsum_bset' C β₂ χ (fun η => ClassFunction.inner χ (delta C β₂ η) * η 1)]
  exact Finset.sum_nbij (fun a => ws41_tvI C β₂ a)
    (ws41_tvI_mapsTo D C β₂ hc hn hβ f hf χ hχ hne)
    (ws41_tvI_injOn D C β₂ hc hn hβ f hf χ hχ hne)
    (ws41_tvI_surjOn D C β₂ hc hn hβ f hf χ hχ hne)
    (fun a ha => by
      rw [ws41_tvI_coe C β₂ a]
      exact ws41_term D C β₂ hc hn hβ f hf χ hχ hall ((ws41_mem_Tfin C).mp ha))

/-- Lemma 4.1 (iv): `χ(1)` is odd. -/
theorem ws41_part_iv (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (hne : (bset' C β₂ χ).Nonempty) :
    ∃ d : ℤ, Odd d ∧ χ 1 = d := by
  have hpi := ws41_part_i D C β₂ hc hn hβ f hf χ hχ hne
  have hone : (((1 : ↥C.P.H0)) : G) ∈ C.P.U := by
    rw [show (((1 : ↥C.P.H0)) : G) = 1 from rfl]
    exact Subgroup.one_mem C.P.U
  have hcong := (lemma24 C f hf χ hχ).2.2 (1 : ↥C.P.H0) hone
  have hsum_T : (ws41_Tfin C f χ).sum
        (fun ξ : IrreducibleCharacter ↥C.P.H0 => ξ.toClassFunction (1 : ↥C.P.H0))
      = (ws41_Sfin C β₂ χ).sum
        (fun η : IrreducibleCharacter ↥C.P.H0 => η.toClassFunction (1 : ↥C.P.H0)) :=
    Finset.sum_nbij (fun a => ws41_tvI C β₂ a)
      (ws41_tvI_mapsTo D C β₂ hc hn hβ f hf χ hχ hne)
      (ws41_tvI_injOn D C β₂ hc hn hβ f hf χ hχ hne)
      (ws41_tvI_surjOn D C β₂ hc hn hβ f hf χ hχ hne)
      (fun a _ => by rw [ws41_tvI_coe C β₂ a, ws41_tv_apply_one])
  have hexg : ∀ η : IrreducibleCharacter ↥C.P.H0, ∃ d : ℤ,
      η ∈ ws41_Sfin C β₂ χ → (η.toClassFunction (1 : ↥C.P.H0) = (d : ℂ) ∧ Odd d) := by
    intro η
    by_cases hη : η ∈ ws41_Sfin C β₂ χ
    · obtain ⟨d, hd, hval⟩ := l41_s4Index_one_odd D C hc hn ((ws41_mem_Sfin C).mp hη).1
      exact ⟨d, fun _ => ⟨hval, hd⟩⟩
    · exact ⟨0, fun h => absurd h hη⟩
  let g : IrreducibleCharacter ↥C.P.H0 → ℤ := fun η => Classical.choose (hexg η)
  have hg : ∀ η ∈ ws41_Sfin C β₂ χ,
      η.toClassFunction (1 : ↥C.P.H0) = (g η : ℂ) ∧ Odd (g η) :=
    fun η hη => Classical.choose_spec (hexg η) hη
  have hodd_card : Odd (ws41_Sfin C β₂ χ).card := by
    rw [← ws41_ncard_bset' C β₂ χ]
    rcases hpi with h | h <;> rw [h] <;> norm_num
  have hodd_int : Odd (∑ η ∈ ws41_Sfin C β₂ χ, g η) :=
    ws41_odd_sum _ g (fun η hη => (hg η hη).2) hodd_card
  have hsum_int : (ws41_Sfin C β₂ χ).sum
        (fun η : IrreducibleCharacter ↥C.P.H0 => η.toClassFunction (1 : ↥C.P.H0))
      = ((∑ η ∈ ws41_Sfin C β₂ χ, g η : ℤ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun η hη => (hg η hη).1)]
    push_cast
    ring
  have hsum_final : (∑ᶠ ν ∈ bset C f χ, ν (1 : ↥C.P.H0))
      = ((∑ η ∈ ws41_Sfin C β₂ χ, g η : ℤ) : ℂ) := by
    rw [ws41_finsum_bset C f χ (fun ξ => ξ (1 : ↥C.P.H0)), hsum_T, hsum_int]
  have hchi_int : ∃ m : ℤ, χ (1 : G) = (m : ℂ) := by
    rcases hχ with hχ0 | hχ0
    · obtain ⟨n, -, hval, -⟩ := hχ0.exists_natDegree_charValue_one_dvd_card
      exact ⟨n, hval⟩
    · obtain ⟨n, -, hval, -⟩ := hχ0.exists_natDegree_charValue_one_dvd_card
      refine ⟨-(n : ℤ), ?_⟩
      have h1 : χ (1 : G) = -((-χ) (1 : G)) := by simp
      rw [h1, hval]; push_cast; ring
  obtain ⟨m, hm⟩ := hchi_int
  have hcong' : AlgIntModTwo ((m : ℤ) : ℂ) ((∑ η ∈ ws41_Sfin C β₂ χ, g η : ℤ) : ℂ) := by
    rw [← hm, ← hsum_final]
    simpa using hcong
  exact ⟨m, ws41_odd_of_algIntModTwo hcong' hodd_int, hm⟩

end Main




end Sec4

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem wsL41Val {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Lemma41Prop D C := by
  intro hc hn β₂ hβ χ hχ hne
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥C.P.H0) := finite_irreducibleCharacter (G := ↥C.P.H0)
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  obtain ⟨f, hf⟩ := l41_isCoherent_exists D C hc hn hβ
  exact ⟨ws41_part_i D C β₂ hc hn hβ f hf χ hχ hne,
    ws41_part_ii D C β₂ hc hn hβ f hf χ hχ hne,
    ws41_part_iv D C β₂ hc hn hβ f hf χ hχ hne⟩

end Work.BG
