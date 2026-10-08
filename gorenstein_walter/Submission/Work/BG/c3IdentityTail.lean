import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.c3Identity
import Submission.Work.BG.s02_bsValueAtT
import Submission.Work.BG.lemma22Kappa
import Submission.Work.BG.constituentSum
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.exists_lamCF_t_neg_one_sconj_ne
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.glaubValue
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.CharBridge
import Submission.Work.BG.c3ExcFour
import Submission.Work.BG.c3ExcNeFour
import Submission.Work.BG.nCases
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_bset_finite
import Submission.Work.GLUE.Defs

/-!
# The identity (6) for a *given* constituent `χ₁` of `f κ`

`Work.BG.c3IdentityTail` is the "tail" of `Work.GW2.C16.C3IdentityProp` (BG 1981, pp. 210–211,
fact (6) of the proof of Theorem C in the case `|S| ≥ 8`): where `C3IdentityProp` *produces* a
signed irreducible constituent `χ₁` of `f κ = κ̃₁` together with its partner `χ₂` and the
identity (6), the present statement starts from a **given** signed irreducible `χ₁` with
`(χ₁, f κ) = 1` and produces the partner `χ₂`, the character `χ₃ = f (λ_β κ)` (`λ_β(t) = -1`)
and the identity

  `(D.H.index) * (χ₁(t)²/χ₁(1) + χ₂(t)²/χ₂(1) − 4/χ₃(1)) = 2 k²`.

## Route

* `exists_lamCF_t_neg_one_sconj_ne` supplies `β` with `λ_β(t) = -1` (and `sconj λ_β ≠ λ_β`);
  `ν := λ_β κ` then has `ν(t) = -1` and `ν^s ≠ ν`.
* The `Λ`-action is free on `κ` (if `λ_β κ = λ_β' κ` then `β = β'`, because `κ = 1` on `S₀`
  and `S₀ ↠ H₀/U`), so `|Λν| = |Λ| = |H₀ : U| = D.n` (`rem31StabCard`, `rem31IndexUin`).
* Coherence gives `f ν ∈ ℤ[Irr G]` with norm `1` (as `sconj C ν ≠ ν`), so `f ν ∈ ±Irr G`;
  `f ν (t) = 2 ν(t) = -2` is BG Lemma 3.4 / coherence `(vi)` (`c3L34Prop`, assembled below
  from Theorem 3.2, Lemma 3.4's exceptional configuration and Lemma 2.4).
* `f κ` has norm `2`, and `χ₂ := f κ − χ₁` is again a signed irreducible orthogonal to `χ₁`
  (`subPmIrrAux`).
* Lemma 2.2 (`lemma22Kappa`) applied to the pair `(κ, λ_β κ)` together with the constituent
  sum identity X1 (`constituentSum`) for the three signed irreducibles
  `(χ₁, χ₂, −f ν)` gives (6).
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-! ## 1. Elementary character-theoretic helpers -/

/-- `IsPmIrr` is invariant under negation. -/
private theorem isPmIrr_negAux {K : Type} [Group K] {φ : ClassFunction K ℂ}
    (h : IsPmIrr φ) : IsPmIrr (-φ) := by
  rcases h with h | h
  · exact Or.inr (by simpa using h)
  · exact Or.inl h

/-- **The partner of a constituent.**  If `φ ∈ ℤ[Irr K]` has squared norm `2` and `χ ∈ ±Irr K`
is a constituent of `φ` with multiplicity `1` (`⟨χ, φ⟩ = 1`), then `φ - χ` is again a signed
irreducible, orthogonal to `χ`. -/
private theorem subPmIrrAux {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ χ : ClassFunction K ℂ}
    (hφ : φ ∈ ZIrr K) (hnorm : ClassFunction.inner φ φ = 2)
    (hχ : IsPmIrr χ) (hinner : ClassFunction.inner χ φ = 1) :
    IsPmIrr (φ - χ) ∧ ClassFunction.inner χ (φ - χ) = 0 := by
  have hχZ : χ ∈ ZIrr K := IsPmIrr.mem_ZIrr hχ
  have hχnorm : ClassFunction.inner χ χ = 1 := IsPmIrr.inner_self hχ
  -- symmetry of the pairing, the values being real integers here
  have hχφ : ClassFunction.inner φ χ = 1 := by
    have h := ClassFunction.inner_star_comm (G := K) χ φ
    rw [hinner] at h
    simpa using congrArg star h.symm
  have hsub : φ - χ ∈ ZIrr K := Submodule.sub_mem _ hφ hχZ
  have hnorm' : ClassFunction.inner (φ - χ) (φ - χ) = 1 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hnorm, hχφ, hinner, hχnorm]
    ring
  refine ⟨isPmIrr_of_mem_ZIrr_inner_self_eq_one hsub hnorm', ?_⟩
  rw [ClassFunction.inner_sub_right, hinner, hχnorm, sub_self]

/-- **X1 (`ConstituentSumProp`) in three-term form.** -/
private theorem constituentSum3Aux {K : Type} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] [Fintype (IrreducibleCharacter K)]
    (ε₁ ε₂ ε₃ : ClassFunction K ℂ) (h1 : IsPmIrr ε₁) (h2 : IsPmIrr ε₂)
    (h3 : IsPmIrr ε₃) (g : K) :
    ∑ χ : IrreducibleCharacter K, (χ : ClassFunction K ℂ) g ^ 2 / (χ : ClassFunction K ℂ) 1 *
        ClassFunction.inner (ε₁ + ε₂ + ε₃) (χ : ClassFunction K ℂ) =
      ε₁ g ^ 2 / ε₁ 1 + ε₂ g ^ 2 / ε₂ 1 + ε₃ g ^ 2 / ε₃ 1 := by
  have hε : ∀ i : Fin 3, IsPmIrr ((![ε₁, ε₂, ε₃] : Fin 3 → ClassFunction K ℂ) i) := by
    intro i
    fin_cases i <;> simp [h1, h2, h3]
  have h := constituentSum (K := K) (ι := Fin 3)
    (![ε₁, ε₂, ε₃] : Fin 3 → ClassFunction K ℂ) hε g
  simpa [Fin.sum_univ_three] using h

/-! ## 2. The `Λ`-orbit of `κ` -/

/-- **Cancellation of the `Λ`-action on `κ`.**  If `κ` is trivial on `S₀ = D.S0` then
`λ_γ κ = λ_{γ'} κ` forces `γ = γ'`: evaluating on the elements of `S₀` (where `κ = 1`) shows
`λ_γ = λ_{γ'}` on `S₀`, and since `H₀/U` is the image of `S₀` (as `H₀ = U · S₀`) while all `λ`
are trivial on `U`, this gives `γ = γ'`. -/
private theorem tailCancel {G : Type} [Group G] [Finite G] (D : BGData G)
    (C : Sec2Ctx G) (hcompat : Compat D C) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1)
    {γ γ' : quotGroup C.P →* ℂˣ} (h : lamCF C γ * κ = lamCF C γ' * κ) : γ = γ' := by
  have hval' : ∀ s : ↥C.P.H0, (s : G) ∈ D.S0 → γ (quotMk C.P s) = γ' (quotMk C.P s) := by
    intro s hs
    have h' := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ s) h
    simp only [ClassFunction.mul_apply] at h'
    rw [hκS0 s hs] at h'
    rw [lamCF_apply, lamCF_apply] at h'
    exact Units.ext (by simpa using h')
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) z
  obtain ⟨u, hu, s, hs, hus⟩ := LamCFFixed.H0_decomp D C hcompat x
  have hu1 : quotMk C.P u = 1 :=
    (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
  have hπ : quotMk C.P x = quotMk C.P s := by rw [← hus, map_mul, hu1, one_mul]
  calc γ (quotMk C.P x) = γ (quotMk C.P s) := by rw [hπ]
    _ = γ' (quotMk C.P s) := hval' s hs
    _ = γ' (quotMk C.P x) := by rw [hπ]

/-- **`|Λκ| = n`.**  For `κ` trivial on `S₀` the `Λ`-action on `κ` is free, so the orbit has
`|Λ| = |H₀ : U| = n = D.n` elements. -/
private theorem tailOrbitCard {G : Type} [Group G] [Finite G] (D : BGData G)
    (C : Sec2Ctx G) (hcompat : Compat D C) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1) :
    (lamOrbit C κ).ncard = D.n := by
  have hfree : ∀ β : quotGroup C.P →* ℂˣ, lamCF C β * κ = κ → β = 1 := by
    intro β hβ
    refine MonoidHom.ext fun z => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) z
    obtain ⟨u, hu, s, hs, hus⟩ := LamCFFixed.H0_decomp D C hcompat x
    have hu1 : quotMk C.P u = 1 :=
      (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
    have hπ : quotMk C.P x = quotMk C.P s := by rw [← hus, map_mul, hu1, one_mul]
    rw [hπ]
    have hval := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ s) hβ
    simp only [ClassFunction.mul_apply] at hval
    rw [lamCF_apply, hκS0 s hs, mul_one] at hval
    refine Units.ext ?_
    simpa using hval
  have hstab : Nat.card ↥(lamStab C κ) = 1 := by
    rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
    intro β hβ
    exact hfree β ((mem_lamStab C κ β).mp hβ)
  have h := rem31StabCard C κ
  rw [hstab, one_mul] at h
  rw [h, rem31IndexUin D C hcompat]

/-! ## 3. BG Lemma 3.4, value form

The two sub-cases of the *exceptional configuration* of BG Lemma 3.4 (`|Λν| = 4` and
`(Λν)^s = Λν`, the paper's separate computation on `|S| = 8`, pp. 209–210) are the library
lemmas `Work.BG.c3ExcFour` (`|Λξ| = 4`) and `Work.BG.c3ExcNeFourB` (`|Λξ| ≠ 4`); a third,
non-`s`-fixed member is excluded by Theorem 3.2 (`Work.BG.l34_no_third_nonfixed`). -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **The exceptional configuration** (BG Lemma 3.4, pp. 209–210): a third, `s`-fixed member
`ξ ∈ 𝒮(χ) ∖ {ν, ν^s}` does not exist when `|Λν| = 4` and `(Λν)^s = Λν`. -/
private theorem excLocal {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Compat D C → Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, IsPmIrr χ →
    ∀ ν ∈ bset C f χ, sconj C ν ≠ ν →
      (sconj C ν ∉ lamOrbit C ν ∨ (lamOrbit C ν).ncard = D.n) →
      (lamOrbit C ν).ncard = 4 →
      sconj C '' lamOrbit C ν = lamOrbit C ν →
      ∀ ξ ∈ bset C f χ, ξ ≠ ν → ξ ≠ sconj C ν → False := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs
  by_cases hfix : sconj C ξ = ξ
  · by_cases hξ4 : (lamOrbit C ξ).ncard = 4
    · exact c3ExcFour D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs hfix hξ4
    · exact c3ExcNeFour D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs hfix hξ4
  · exact l34_no_third_nonfixed D C hDC hS3 f hf χ hχ ν hν hne ξ hξ hξν hξνs hfix

/-- **BG Lemma 3.4, value form.**  For `χ ∈ ±Irr(G)` and `ν ∈ 𝒮(χ)` with `ν^s ≠ ν` and
`ν^s ∉ Λν` or `|Λν| = m`, one has `f ν (t) = 2 ν(t)`.  (The companion assertion
`𝒮(χ) = {ν, ν^s}` is not needed here.) -/
private theorem l34ValueLocal {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter G)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (ν : ClassFunction ↥C.P.H0 ℂ) (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (hdisj : sconj C ν ∉ lamOrbit C ν ∨ (lamOrbit C ν).ncard = D.n) :
    f ν (C.t : G) = 2 * ν C.t := by
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
    rcases l34_eq_pm_of_inner_ne_zero hZIfν hnormf1 hχ hνne0 with h | h
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
  by_cases hexc : (lamOrbit C ν).ncard = 4 ∧ sconj C '' lamOrbit C ν = lamOrbit C ν
  · by_cases hbset : bset C f χ = {ν, sconj C ν}
    · -- only `ν`, `ν^s` occur in `𝒮(χ)`: Lemma 2.4 for `f ν` at `t`
      have hbsetν : bset C f (f ν) = {ν, sconj C ν} := by rw [hbset_eq]; exact hbset
      have hT := (lemma24 C f hf (f ν) hpmfν).2.1 C.t C.t_not_mem_U
      have hnot1 : ν ∉ ({sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
        intro hmem
        rw [Set.mem_singleton_iff] at hmem
        exact hne hmem.symm
      have hsum : (∑ᶠ η ∈ bset C f (f ν), ClassFunction.inner (f ν) (f η) * η C.t)
          = 2 * ν C.t := by
        rw [hbsetν,
          finsum_mem_insert (f := fun η => ClassFunction.inner (f ν) (f η) * η C.t)
            (a := ν) (s := ({sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)))
            hnot1 (Set.toFinite _),
          finsum_mem_singleton,
          hsconjf, hnormf1, sconj_apply_t]
        ring
      rw [hsum] at hT
      exact hT
    · -- the exceptional configuration: `𝒮(χ)` cannot contain a third character
      have hne_sub : ¬ ((bset C f χ) ⊆ ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ))) :=
        fun hsub => hbset (Set.Subset.antisymm hsub hsub2)
      obtain ⟨ξ, hξmem, hξnot⟩ := Set.not_subset.mp hne_sub
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hξnot
      exact (excLocal D C hDC hS3 f hf χ hχ ν ⟨hνirr, hνne0⟩ hne hdisj hexc.1 hexc.2 ξ
        hξmem (fun h => hξnot (Or.inl h)) (fun h => hξnot (Or.inr h))).elim
  · exact hvi hne hexc

/-! ## 4. The main theorem -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3IdentityTail {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (K1 K2 : Subgroup G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Work.GW2.C16.Compat D C) (hn4 : 4 ≤ D.n) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκ : Work.GW2.C16.IsKappa D C κ)
    (χ₁ : ClassFunction G ℂ) (hχ₁ : Work.BG.IsPmIrr χ₁)
    (hinner : ClassFunction.inner χ₁ (f κ) = 1) [Fintype (IrreducibleCharacter G)] :
    ∃ (χ₂ χ₃ : ClassFunction G ℂ) (β : Work.BG.quotGroup C.P →* ℂˣ),
      Work.BG.IsPmIrr χ₂ ∧ ClassFunction.inner χ₁ χ₂ = 0 ∧ f κ = χ₁ + χ₂ ∧
      Work.BG.lamCF C β C.t = -1 ∧ χ₃ = f (Work.BG.lamCF C β * κ) ∧
        Work.BG.IsPmIrr χ₃ ∧
      (D.H.index : ℂ) * (χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 - 4 / χ₃ 1) =
        2 * (D.k : ℂ) ^ 2 := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  obtain ⟨β, hβt, hβnotfix⟩ := exists_lamCF_t_neg_one_sconj_ne D C hComp hn4
  obtain ⟨hκirr, hκ1, hκsconj, hκS0, _hκne⟩ := hκ
  -- ## `ν := λ_β κ`
  let ν : ClassFunction ↥C.P.H0 ℂ := lamCF C β * κ
  have hLam : LamEquiv C κ ν := ⟨β, rfl⟩
  have hνirr : IsIrreducibleCharacter ν := lambda_mul_irreducible C.P ⟨β, rfl⟩ hκirr
  have hκt : κ C.t = 1 := hκS0 C.t (by rw [hComp.t_eq]; exact D.t_mem)
  have hνt : ν C.t = -1 := by
    change (lamCF C β * κ) C.t = -1
    rw [ClassFunction.mul_apply, hκt, mul_one]
    exact hβt
  -- `ν` is not `s`-fixed
  have hsconj : sconj C ν ≠ ν := by
    intro hfix
    change sconj C (lamCF C β * κ) = lamCF C β * κ at hfix
    rw [sconjLam C β κ, hκsconj] at hfix
    have h2 : β⁻¹ = β := tailCancel D C hComp κ hκS0 hfix
    refine hβnotfix ?_
    rw [LamCFFixed.sconj_lamCF C β, h2]
  -- ## `|Λν| = D.n`
  have horbκ : (lamOrbit C κ).ncard = D.n := tailOrbitCard D C hComp κ hκS0
  have horb : (lamOrbit C ν).ncard = D.n := by
    rw [← s02c_lamOrbit_eq_of_lamEquiv C hLam]
    exact horbκ
  -- ## The value `f ν (t) = -2`
  have hνkey : ν ∈ orbitKey C ν := Or.inl (s02c_LamEquiv_refl C ν)
  have hνgood := (hf.1 ν hνirr) ν hνkey ν hνkey hνirr hνirr
  have hnorm1 : ClassFunction.inner (f ν) (f ν) = 1 := by
    rw [hνgood.2.2.1, if_neg hsconj]
  have hpmν : IsPmIrr (f ν) := isPmIrr_of_mem_ZIrr_inner_self_eq_one hνgood.1 hnorm1
  have hνmem : ν ∈ bset C f (f ν) := ⟨hνirr, by rw [hnorm1]; norm_num⟩
  have hval : f ν (C.t : G) = 2 * ν C.t :=
    l34ValueLocal D C hComp hS3 f hf (f ν) hpmν ν hνmem hsconj (Or.inr horb)
  have hνval : f ν (C.t : G) = -2 := by rw [hval, hνt]; norm_num
  -- ## The decomposition `f κ = χ₁ + χ₂`
  have hκkey : κ ∈ orbitKey C κ := Or.inl (s02c_LamEquiv_refl C κ)
  have hκgood := (hf.1 κ hκirr) κ hκkey κ hκkey hκirr hκirr
  have hnormκ : ClassFunction.inner (f κ) (f κ) = 2 := by
    rw [hκgood.2.2.1, if_pos hκsconj]
  obtain ⟨hpm2, horth⟩ := subPmIrrAux hκgood.1 hnormκ hχ₁ hinner
  have hsum : f κ = χ₁ + (f κ - χ₁) := by abel
  -- ## Coherence at the pair `(κ, ν)`, and Lemma 2.2
  have hind : ind C (κ - ν) = f κ - f ν := by
    have hGκν := (hf.1 κ hκirr) κ hκkey ν (Or.inl hLam) hκirr hνirr
    exact hGκν.2.2.2.1 hLam
  have h22 := lemma22Kappa D C hComp κ β hκirr hκ1 hκsconj hκS0 (Or.inl hsconj)
  -- ## The constituent sum identity X1 for the three signed irreducibles `(χ₁, χ₂, -f ν)`
  have hX1 := constituentSum3Aux (K := G) χ₁ (f κ - χ₁) (-(f ν)) hχ₁ hpm2
    (isPmIrr_negAux hpmν) (C.t : G)
  have hnum : (-(f ν (C.t : G))) ^ 2 = 4 := by rw [hνval]; norm_num
  have h3 : (-(f ν)) (C.t : G) ^ 2 / (-(f ν)) 1 = -(4 / (f ν) 1) := by
    rw [ClassFunction.neg_apply, ClassFunction.neg_apply, hnum, div_neg]
  have hsumε : χ₁ + (f κ - χ₁) + -(f ν) = ind C (κ - ν) := by
    rw [hind, hsum]
    abel
  rw [h3] at hX1
  rw [hsumε] at hX1
  -- ## Conclusion
  refine ⟨f κ - χ₁, f ν, β, hpm2, horth, hsum, hβt, rfl, hpmν, ?_⟩
  have hbr : χ₁ (C.t : G) ^ 2 / χ₁ 1 + (f κ - χ₁) (C.t : G) ^ 2 / (f κ - χ₁) 1 -
        4 / (f ν) 1 =
      χ₁ (C.t : G) ^ 2 / χ₁ 1 + (f κ - χ₁) (C.t : G) ^ 2 / (f κ - χ₁) 1 +
        (-(4 / (f ν) 1)) := by
    rw [sub_eq_add_neg]
  rw [hbr, ← hX1]
  exact h22

end Work.BG
