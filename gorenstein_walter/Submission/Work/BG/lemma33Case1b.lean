import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma24
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.glaubValue
import Submission.Work.BG.glaubCorrDistinct
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.lemma33ShapeA
import Submission.Work.BG.lemma33Arith
import Submission.Work.BG.lemma33Aux
import Submission.Work.BG.l33Setup
import Submission.Work.BG.thm32
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.s02_sum_irr_eq_finsum_bset

/-!
# Area BG: Bender–Glauberman 1981, Lemma 3.3, first case

`Work.BG.lemma33Case1b` is the first case of BG Lemma 3.3 (p. 209): if `𝒮(χ) = bset C f χ`
contains two distinct `s`-fixed characters `ν₁, ν₂` with `|Λνᵢ| = m = D.n`, and no third such
character, then `False`.

The paper's proof: `ν₁|_U` and `ν₂|_U` are distinct `S`-invariant irreducible characters of
`U` (Remark 3.1 for `|Λν| = m`), Lemma 2.4 together with Lemmas 1.8/1.9 give
`χ ≡ ν₁ + ν₂ ≢ 0 (mod 2)` on `B = C_U(S)`, while Gorenstein 4.2.10 forces `χ ≡ 0 (mod 2)` on `B`
(`χ(1)` is even and `|G : C_G(g)|` is odd for `g ∈ B`) — a contradiction.

The formal ingredients (proved elsewhere in the fleet's library, and imported here):

* `Work.BG.lemma33ShapeA`: for `|Λν| = D.n`, `ν|_U` is a single `H₀`-invariant irreducible `a`;
* `Work.BG.rem31Shape`: Remark 3.1's shape dichotomy `ν|_U = a` or `ν|_U = a + a₂`
  (with `a₂(1) = a(1)` and `2|Λν| = D.n`);
* `Work.BG.l33Setup`: the `S`-action `φ_S` on `U` by conjugation and its fixed points `C_U(S)`;
* `Work.BG.glaubCorrDistinct`: injectivity of Glauberman's mod-2 correspondence;
* `Work.BG.lemma33Arith`: Gorenstein 4.2.10 in the form needed (`χ(1)` even and `|G : C_G(g)|`
  odd force `χ(g) ≡ 0 (mod 2)`).

The parity bookkeeping on the fixed-point subgroup `C_U(S)` splits `𝒮(χ)` into the `s`-fixed
part and the pairs `{ν, ν^s}`: on `C_U(S)` a pair contributes `2ν(u)`, and a member with
`2|Λν| = D.n` contributes `2a(u)` (`Work.BG.l33_even`); only `ν₁, ν₂` remain, which is where the
hypothesis on the absence of a third such character is used.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. The coset decomposition `S = S₀ ∪ S₀ t₁` -/

/-- Every element of `S` is in `S₀` or of the form `z * t₁` with `z ∈ S₀`.

`S₀` has index `2` in `S` (`D.S0_index`) and `t₁ ∉ S₀`; the relative version of
`Subgroup.mul_mem_iff_of_index_two` gives `s * t₁ ∈ S₀` for `s ∈ S ∖ S₀`, whence
`s = (s * t₁) * t₁`. -/
theorem l33_S_decomp (D : BGData G) {s : G} (hs : s ∈ (D.S : Subgroup G)) :
    s ∈ D.S0 ∨ ∃ z ∈ D.S0, s = z * D.t1 := by
  by_cases hs0 : s ∈ D.S0
  · exact Or.inl hs0
  · refine Or.inr ⟨s * D.t1, ?_, ?_⟩
    · have hind : (D.S0.subgroupOf (D.S : Subgroup G)).index = 2 := D.S0_index
      have hiff := Subgroup.mul_mem_iff_of_index_two hind
        (a := (⟨s, hs⟩ : ↥(D.S : Subgroup G))) (b := (⟨D.t1, D.t1_mem⟩ : ↥(D.S : Subgroup G)))
      have : (⟨s, hs⟩ : ↥(D.S : Subgroup G)) * ⟨D.t1, D.t1_mem⟩ ∈
          D.S0.subgroupOf (D.S : Subgroup G) := by
        rw [hiff]
        exact ⟨fun h => absurd (Subgroup.mem_subgroupOf.mp h) hs0,
          fun h => absurd (Subgroup.mem_subgroupOf.mp h) D.t1_nmem⟩
      simpa using Subgroup.mem_subgroupOf.mp this
    · have ht1 : D.t1 * D.t1 = 1 := by
        have h := pow_orderOf_eq_one D.t1
        rw [D.t1_order] at h
        simpa [pow_two] using h
      rw [mul_assoc, ht1, mul_one]

/-! ## 2. Invariance of the restriction under the `S`-action -/

/-- If `(s : G) ∈ H₀`, the `S`-action `φ_S s ∈ MulAut U` is conjugation inside `H₀`. -/
theorem l33_phiS_eq_conjBy (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (s : ↥(D.S)) (hgH : (s : G) ∈ C.P.H0) (v : ↥(Uin C)) :
    l33_phiS D C hDC s v =
      ClassFunction.conjByMulEquiv (G := ↥C.P.H0) (H := Uin C) (⟨(s : G), hgH⟩ : ↥C.P.H0) v := by
  apply Subtype.ext
  apply Subtype.ext
  rw [l33_phiS_apply D C hDC s v]
  rw [ClassFunction.conjByMulEquiv_apply]
  rfl

/-- Invariance under the elements of `S ∩ H₀ = S₀`: `H₀`-invariance of `a`. -/
theorem l33_H0_inv (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {a : ClassFunction ↥(Uin C) ℂ}
    (hH0 : ∀ g : ↥C.P.H0, ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) g a = a)
    (s : ↥(D.S)) (hgH : (s : G) ∈ C.P.H0) (v : ↥(Uin C)) :
    a (l33_phiS D C hDC s v) = a v := by
  rw [l33_phiS_eq_conjBy D C hDC s hgH v]
  show (ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) (⟨(s : G), hgH⟩ : ↥C.P.H0) a) v = a v
  rw [hH0]

/-- Invariance under `t₁`: this is the `s`-fixedness of `ν`. -/
theorem l33_t1_inv (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {ν : ClassFunction ↥C.P.H0 ℂ} {a : ClassFunction ↥(Uin C) ℂ}
    (hres : ClassFunction.restrict (Uin C) ν = a) (hs : sconj C ν = ν) (v : ↥(Uin C)) :
    a (l33_phiS D C hDC ⟨D.t1, D.t1_mem⟩ v) = a v := by
  have hval : ((l33_phiS D C hDC ⟨D.t1, D.t1_mem⟩ v : ↥(Uin C)) : ↥C.P.H0)
      = conjMulEquiv C.P C.s v := by
    apply Subtype.ext
    rw [l33_phiS_apply D C hDC ⟨D.t1, D.t1_mem⟩ v, conjMulEquiv_apply, hDC.s_eq]
  calc a (l33_phiS D C hDC ⟨D.t1, D.t1_mem⟩ v)
      = ClassFunction.restrict (Uin C) ν (l33_phiS D C hDC ⟨D.t1, D.t1_mem⟩ v) := by rw [hres]
    _ = ν ((l33_phiS D C hDC ⟨D.t1, D.t1_mem⟩ v : ↥(Uin C)) : ↥C.P.H0) :=
        ClassFunction.restrict_apply _ _ _
    _ = ν (conjMulEquiv C.P C.s v) := by rw [hval]
    _ = sconj C ν v := by rw [sconj, conjByH]; rfl
    _ = ν v := by rw [hs]
    _ = ClassFunction.restrict (Uin C) ν v := (ClassFunction.restrict_apply _ _ _).symm
    _ = a v := by rw [hres]

/-- The restriction `ν|_U = a` of an `s`-fixed irreducible `ν` with `H₀`-invariant `a` is
invariant under the whole `S`-action: `S = S₀ ∪ S₀t₁`, and both `S₀` (through `a`'s
`H₀`-invariance) and `t₁` (through `ν^s = ν`) fix `a`. -/
theorem l33_restrict_invariant (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    {ν : ClassFunction ↥C.P.H0 ℂ} {a : ClassFunction ↥(Uin C) ℂ}
    (hres : ClassFunction.restrict (Uin C) ν = a) (hs : sconj C ν = ν)
    (hH0 : ∀ g : ↥C.P.H0, ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) g a = a) :
    ∀ (s : ↥(D.S)) (v : ↥(Uin C)), a (l33_phiS D C hDC s v) = a v := by
  intro s v
  rcases l33_S_decomp D s.2 with hs0 | ⟨z, hz0, hsz⟩
  · have hsinH0 : (s : G) ∈ C.P.H0 := by
      rw [hDC.H0_eq]
      exact Subgroup.mem_sup_right hs0
    exact l33_H0_inv D C hDC hH0 s hsinH0 v
  · have hzH0 : z ∈ C.P.H0 := by
      rw [hDC.H0_eq]
      exact Subgroup.mem_sup_right hz0
    have hzS : z ∈ (D.S : Subgroup G) := D.S0_le hz0
    have hdecomp : l33_phiS D C hDC s v =
        l33_phiS D C hDC ⟨z, hzS⟩ (l33_phiS D C hDC ⟨D.t1, D.t1_mem⟩ v) := by
      apply Subtype.ext
      apply Subtype.ext
      rw [l33_phiS_apply D C hDC s v, l33_phiS_apply D C hDC ⟨z, hzS⟩ _,
        l33_phiS_apply D C hDC ⟨D.t1, D.t1_mem⟩ v]
      rw [hsz]
      group
    rw [hdecomp, l33_H0_inv D C hDC hH0 ⟨z, hzS⟩ hzH0 (l33_phiS D C hDC ⟨D.t1, D.t1_mem⟩ v),
      l33_t1_inv D C hDC hres hs v]

/-! ## 3. The evenness of a member with `2|Λν| = D.n` on `C_U(S)` -/

section Even

variable (D : BGData G) (C : Sec2Ctx G)

/-- `|S₀| = D.n`. -/
theorem l33_card_S0 : Nat.card ↥D.S0 = D.n := by
  have hS : Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
    obtain ⟨e⟩ := D.dih
    rw [Nat.card_congr e.toEquiv]
    exact DihedralGroup.nat_card
  have h2 : Nat.card ↥(D.S0.subgroupOf (D.S : Subgroup G)) *
      (D.S0.subgroupOf (D.S : Subgroup G)).index = Nat.card ↥(D.S : Subgroup G) :=
    Subgroup.card_mul_index _
  have hind : (D.S0.subgroupOf (D.S : Subgroup G)).index = 2 := D.S0_index
  rw [hS, hind] at h2
  have hcard : Nat.card ↥(D.S0.subgroupOf (D.S : Subgroup G)) = Nat.card ↥D.S0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.S0_le).toEquiv
  rw [hcard, Nat.mul_comm 2 D.n] at h2
  exact Nat.eq_of_mul_eq_mul_right (m := 2) (by norm_num) h2

/-- `|H₀| = |U| · D.n`. -/
theorem l33_card_H0 (hDC : Compat D C) :
    Nat.card ↥C.P.H0 = Nat.card ↥(Uin C) * D.n := by
  have h := Subgroup.card_mul_index (Uin C)
  rw [rem31IndexUin D C hDC] at h
  exact h.symm

/-- `[H₀ : S₀] = |U|` (so the index of any subgroup of `H₀` containing `S₀` is odd). -/
theorem l33_index_S0 (hDC : Compat D C) :
    (D.S0.subgroupOf C.P.H0).index = Nat.card ↥(Uin C) := by
  have hS0leH0 : D.S0 ≤ C.P.H0 := by
    intro x hx
    rw [hDC.H0_eq]
    exact Subgroup.mem_sup_right hx
  have hcard : Nat.card ↥(D.S0.subgroupOf C.P.H0) = Nat.card ↥D.S0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0leH0).toEquiv
  have h := Subgroup.card_mul_index (D.S0.subgroupOf C.P.H0)
  rw [hcard, l33_card_S0 D, l33_card_H0 D C hDC,
    Nat.mul_comm (Nat.card ↥(Uin C)) D.n] at h
  exact Nat.eq_of_mul_eq_mul_left (n := D.n) (by have h2 := D.two_le; omega) h

/-- **The evenness step.**  If `ν ∈ Irr(H₀)` has `2 · |Λν| = D.n`, then `ν(h)` is even for every
`h ∈ U` centralized by `S`.

By Remark 3.1 (`Work.BG.rem31Shape`) `ν|_U = a + a₂` with `a₂(1) = a(1)`, so `ν(1) = 2a(1)` is
even; and `S₀ ≤ C_{H₀}(h)` (because `S₀ ⊆ S` centralizes `h`), so
`[H₀ : C_{H₀}(h)] ∣ [H₀ : S₀] = |U|` is odd.  Gorenstein 4.2.10 applied in `H₀`
(`Work.BG.algIntModTwo_of_isIrreducibleCharacter_of_even_degree_of_odd_index`) gives the claim. -/
theorem l33_even [Fintype G] [Invertible (Nat.card G : ℂ)] (hDC : Compat D C) (hS3 : Sec3Hyp D)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    (hn : 2 * (lamOrbit C ν).ncard = D.n) :
    ∀ h : ↥C.P.H0, (h : G) ∈ C.P.U →
      (∀ s ∈ (D.S : Subgroup G), s * (h : G) * s⁻¹ = (h : G)) → AlgIntModTwo (ν h) 0 := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro h hhU hcomm
  obtain ⟨a, ha, hcase⟩ := rem31Shape D C hDC hS3 ν hν
  rcases hcase with ⟨_, hn1⟩ | ⟨a₂, ha₂, _, hdeg, hres, _⟩
  · rw [hn1] at hn
    have hzero : D.n = 0 := by omega
    have h2 := D.two_le
    omega
  · have hν1 : AlgIntModTwo (ν 1) 0 := by
      have h1 : ν (1 : ↥C.P.H0) = a 1 + a₂ 1 := by
        have h := congrArg (fun f : ClassFunction ↥(Uin C) ℂ => f 1) hres
        simpa [ClassFunction.add_apply] using h
      rw [h1, hdeg]
      have htwo : a 1 + a 1 = 2 * a 1 := by ring
      rw [htwo]
      exact AlgIntModTwo.mul_two (isIntegral_apply_of_isIrreducibleCharacter' ha 1)
    have hle : D.S0.subgroupOf C.P.H0 ≤ Subgroup.centralizer ({h} : Set ↥C.P.H0) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hxS : (x : G) ∈ (D.S : Subgroup G) := D.S0_le (Subgroup.mem_subgroupOf.mp hx)
      have hxh := hcomm (x : G) hxS
      have h' : (x : G) * (h : G) = (h : G) * (x : G) := by
        have h2 : ((x : G) * (h : G)) * (x : G)⁻¹ = (h : G) := hxh
        have := congrArg (fun y => y * (x : G)) h2
        simpa [mul_assoc] using this
      exact Subtype.ext h'.symm
    have hodd : Odd (Subgroup.centralizer ({h} : Set ↥C.P.H0)).index :=
      Odd.of_dvd_nat (by rw [l33_index_S0 D C hDC]; exact l33_odd_card_Uin D C hDC)
        (Subgroup.index_dvd_of_le hle)
    exact algIntModTwo_of_isIrreducibleCharacter_of_even_degree_of_odd_index hν hν1 h hodd

end Even

/-! ## 4. The theorem -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma33Case1b {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν₁ ∈ Work.GW2.C16.bset C f χ, ∀ ν₂ ∈ Work.GW2.C16.bset C f χ, ν₁ ≠ ν₂ →
    Work.BG.sconj C ν₁ = ν₁ → Work.BG.sconj C ν₂ = ν₂ →
    (Work.BG.lamOrbit C ν₁).ncard = D.n → (Work.BG.lamOrbit C ν₂).ncard = D.n →
    (∀ ν, ν ∈ Work.GW2.C16.bset C f χ → Work.BG.sconj C ν = ν →
        (Work.BG.lamOrbit C ν).ncard = D.n → ν = ν₁ ∨ ν = ν₂) →
    False := by
  intro hDC hS3 f hf χ hχ ν₁ hν₁ ν₂ hν₂ hne hfix₁ hfix₂ hn₁ hn₂ hmax
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI hInvUin : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype ↥(fixedSubgroupS (l33_phiS D C hDC)) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(fixedSubgroupS (l33_phiS D C hDC)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- **(1)** the two shapes `νᵢ|_U = aᵢ`
  obtain ⟨a₁, ha₁irr, hres₁, hH0₁⟩ := lemma33ShapeA D C hDC hν₁.1 hn₁
  obtain ⟨a₂, ha₂irr, hres₂, hH0₂⟩ := lemma33ShapeA D C hDC hν₂.1 hn₂
  -- **(2)** invariance of `aᵢ` under the `S`-action
  have hinv₁ : ∀ (s : ↥(D.S)) (u : ↥(Uin C)), a₁ (l33_phiS D C hDC s u) = a₁ u :=
    l33_restrict_invariant D C hDC hres₁ hfix₁ hH0₁
  have hinv₂ : ∀ (s : ↥(D.S)) (u : ↥(Uin C)), a₂ (l33_phiS D C hDC s u) = a₂ u :=
    l33_restrict_invariant D C hDC hres₂ hfix₂ hH0₂
  -- **(3)** `ν₁` and `ν₂` are not `Λ`-equivalent, hence `a₁ ≠ a₂`
  have hnl : ¬ LamEquiv C ν₁ ν₂ := by
    intro hL
    have h := (bset_orbit_struct C f hf χ hχ).2 ν₁ hν₁ ν₂ hν₂ hL (Ne.symm hne)
    rw [hfix₁] at h
    exact hne h.symm
  have hne_a : a₁ ≠ a₂ := by
    intro heq
    have hinner : ClassFunction.inner (ClassFunction.restrict (Uin C) ν₁)
        (ClassFunction.restrict (Uin C) ν₂) ≠ 0 := by
      rw [hres₁, hres₂, heq]
      have h1 : ClassFunction.inner a₂ a₂ = 1 := by
        have h2 := irreducibleCharacter_inner_eq_ite
          (⟨a₂, ha₂irr⟩ : IrreducibleCharacter ↥(Uin C)) ⟨a₂, ha₂irr⟩
        simpa using h2
      rw [h1]
      norm_num
    exact hinner ((rem31Orth D C hDC ν₁ ν₂ hν₁.1 hν₂.1).2 hnl)
  -- **(4)** the parity reduction on the fixed points of the action
  have hval : ∀ (ξ : ClassFunction ↥C.P.H0 ℂ) {u : ↥(Uin C)},
      u ∈ fixedSubgroupS (l33_phiS D C hDC) → sconj C ξ (u : ↥C.P.H0) = ξ (u : ↥C.P.H0) :=
    fun ξ u hu => l33_sconj_apply D C hDC hu ξ
  have reduce : ∀ u : ↥(Uin C),
      (∀ s ∈ (D.S : Subgroup G), s * ((u : ↥C.P.H0) : G) * s⁻¹ = ((u : ↥C.P.H0) : G)) →
      AlgIntModTwo (∑ᶠ ν ∈ bset C f χ, ν (u : ↥C.P.H0))
        (ν₁ (u : ↥C.P.H0) + ν₂ (u : ↥C.P.H0)) := by
    intro u hcomm
    have hufix : u ∈ fixedSubgroupS (l33_phiS D C hDC) := (l33_mem_fixed' D C hDC u).mpr hcomm
    haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
    have hfinT : (bset C f χ).Finite := (lemma24 C f hf χ hχ).1
    have hsum_eq : (∑ᶠ ν ∈ bset C f χ, ν (u : ↥C.P.H0))
        = ∑ ν ∈ hfinT.toFinset, ν (u : ↥C.P.H0) :=
      finsum_mem_eq_finite_toFinset_sum (fun ν => ν (u : ↥C.P.H0)) hfinT
    rw [hsum_eq]
    have hsplit : ∑ ν ∈ hfinT.toFinset, ν (u : ↥C.P.H0)
        = ∑ ν ∈ hfinT.toFinset.filter (fun ν => sconj C ν = ν), ν (u : ↥C.P.H0)
          + ∑ ν ∈ hfinT.toFinset.filter (fun ν => ¬ (sconj C ν = ν)),
              ν (u : ↥C.P.H0) := by
      rw [Finset.sum_filter_add_sum_filter_not]
    have hTmem : ∀ ν : ClassFunction ↥C.P.H0 ℂ, ν ∈ hfinT.toFinset ↔ ν ∈ bset C f χ :=
      fun ν => hfinT.mem_toFinset
    have hW : AlgIntModTwo
        (∑ ν ∈ hfinT.toFinset.filter (fun ν => ¬ (sconj C ν = ν)), ν (u : ↥C.P.H0)) 0 := by
      have hf_inv : ∀ x : ClassFunction ↥C.P.H0 ℂ,
          (if sconj C x ∈ bset C f χ then sconj C x (u : ↥C.P.H0) else 0)
            = (if x ∈ bset C f χ then x (u : ↥C.P.H0) else 0) := by
        intro x
        by_cases hx : x ∈ bset C f χ
        · have hsx : sconj C x ∈ bset C f χ := (bset_orbit_struct C f hf χ hχ).1 x hx |>.1
          rw [ite_eq_left hsx, ite_eq_left hx]
          exact hval x hufix
        · have hsx : sconj C x ∉ bset C f χ := by
            intro h
            refine hx ?_
            rw [← sconj_sconj C x]
            exact (bset_orbit_struct C f hf χ hχ).1 (sconj C x) h |>.1
          rw [ite_eq_right hsx, ite_eq_right hx]
      have hint : ∀ x : ClassFunction ↥C.P.H0 ℂ,
          IsIntegral ℤ (if x ∈ bset C f χ then x (u : ↥C.P.H0) else 0) := by
        intro x
        by_cases hx : x ∈ bset C f χ
        · rw [ite_eq_left hx]
          exact OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr
            (IsIrreducibleCharacter.mem_ZIrr hx.1) (u : ↥C.P.H0)
        · rw [ite_eq_right hx]
          exact isIntegral_zero
      obtain ⟨z, hz, hzeq⟩ := even_sum_of_free_involution (sconj C) (sconj_sconj C)
        (fun ν => if ν ∈ bset C f χ then ν (u : ↥C.P.H0) else 0) hf_inv hint
        (hfinT.toFinset.filter (fun ν => ¬ (sconj C ν = ν)))
        (by
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨(hTmem _).mpr ((bset_orbit_struct C f hf χ hχ).1 x ((hTmem x).mp hx.1) |>.1),
            by rw [sconj_sconj C x]; exact fun h => hx.2 h.symm⟩)
        (by
          intro x hx
          rw [Finset.mem_filter] at hx
          exact hx.2)
      have hsame : ∑ ν ∈ hfinT.toFinset.filter (fun ν => ¬ (sconj C ν = ν)),
            ν (u : ↥C.P.H0)
          = ∑ ν ∈ hfinT.toFinset.filter (fun ν => ¬ (sconj C ν = ν)),
              (if ν ∈ bset C f χ then ν (u : ↥C.P.H0) else 0) := by
        refine Finset.sum_congr rfl (fun ν hν => ?_)
        rw [Finset.mem_filter] at hν
        rw [ite_eq_left ((hTmem ν).mp hν.1)]
      rw [hsame, hzeq]
      exact ⟨z, hz, by ring⟩
    have hF : AlgIntModTwo
        (∑ ν ∈ hfinT.toFinset.filter (fun ν => sconj C ν = ν), ν (u : ↥C.P.H0))
        (ν₁ (u : ↥C.P.H0) + ν₂ (u : ↥C.P.H0)) := by
      have hsplit2 : ∑ ν ∈ hfinT.toFinset.filter (fun ν => sconj C ν = ν), ν (u : ↥C.P.H0)
          = ∑ ν ∈ (hfinT.toFinset.filter (fun ν => sconj C ν = ν)).filter
                (fun ν => (lamOrbit C ν).ncard = D.n), ν (u : ↥C.P.H0)
            + ∑ ν ∈ (hfinT.toFinset.filter (fun ν => sconj C ν = ν)).filter
                (fun ν => ¬ ((lamOrbit C ν).ncard = D.n)), ν (u : ↥C.P.H0) := by
        rw [Finset.sum_filter_add_sum_filter_not]
      have hpair : (hfinT.toFinset.filter (fun ν => sconj C ν = ν)).filter
          (fun ν => (lamOrbit C ν).ncard = D.n) = {ν₁, ν₂} := by
        ext ν
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hνT, hνfix⟩, hnν⟩
          exact hmax ν (hTmem ν |>.mp hνT) hνfix hnν
        · rintro (h | h)
          · rw [h]
            exact ⟨⟨hTmem ν₁ |>.mpr hν₁, hfix₁⟩, hn₁⟩
          · rw [h]
            exact ⟨⟨hTmem ν₂ |>.mpr hν₂, hfix₂⟩, hn₂⟩
      have hEv : AlgIntModTwo
          (∑ ν ∈ (hfinT.toFinset.filter (fun ν => sconj C ν = ν)).filter
              (fun ν => ¬ ((lamOrbit C ν).ncard = D.n)), ν (u : ↥C.P.H0)) (0 : ℂ) := by
        have hterm : ∀ ν ∈ (hfinT.toFinset.filter (fun ν => sconj C ν = ν)).filter
            (fun ν => ¬ ((lamOrbit C ν).ncard = D.n)),
            AlgIntModTwo (ν (u : ↥C.P.H0)) (0 : ℂ) := by
          intro ν hν
          rw [Finset.mem_filter, Finset.mem_filter] at hν
          obtain ⟨⟨hνT, _⟩, hnν⟩ := hν
          have hmem : ν ∈ bset C f χ := hTmem ν |>.mp hνT
          have htwo : 2 * (lamOrbit C ν).ncard = D.n := by
            rcases rem31Shape D C hDC hS3 ν hmem.1 with ⟨a, _, hcase⟩
            rcases hcase with ⟨_, hn⟩ | ⟨a₂', _, _, _, _, hn⟩
            · exact absurd hn hnν
            · exact hn
          exact l33_even D C hDC hS3 hmem.1 htwo (u : ↥C.P.H0)
            ((Subgroup.mem_subgroupOf).mp u.2) hcomm
        simpa using AlgIntModTwo.sum
          ((hfinT.toFinset.filter (fun ν => sconj C ν = ν)).filter
            (fun ν => ¬ ((lamOrbit C ν).ncard = D.n))) hterm
      rw [hsplit2, hpair, Finset.sum_pair hne]
      simpa using (AlgIntModTwo.refl _ ((isIntegral_apply_of_isIrreducibleCharacter' hν₁.1
        (u : ↥C.P.H0)).add (isIntegral_apply_of_isIrreducibleCharacter' hν₂.1
          (u : ↥C.P.H0)))).add hEv
    rw [hsplit]
    simpa using hF.add hW
  -- **(5)** `χ(1)` is even
  have hEvenχ1 : AlgIntModTwo (χ 1) 0 := by
    have hcomm1 : ∀ s ∈ (D.S : Subgroup G),
        s * (((1 : ↥(Uin C)) : ↥C.P.H0) : G) * s⁻¹ = (((1 : ↥(Uin C)) : ↥C.P.H0) : G) := by
      intro s hs
      simp
    have hred1 := reduce (1 : ↥(Uin C)) hcomm1
    have h24_1 := (lemma24 C f hf χ hχ).2.2 (1 : ↥C.P.H0) C.P.U.one_mem
    obtain ⟨d₁, hd₁pos, hd₁eq, hd₁dvd⟩ :=
      IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card (G := ↥(Uin C)) ha₁irr
    obtain ⟨d₂, hd₂pos, hd₂eq, hd₂dvd⟩ :=
      IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card (G := ↥(Uin C)) ha₂irr
    have hodd₁ : Odd d₁ := (l33_odd_card_Uin D C hDC).of_dvd_nat hd₁dvd
    have hodd₂ : Odd d₂ := (l33_odd_card_Uin D C hDC).of_dvd_nat hd₂dvd
    have hν₁1 : ν₁ (1 : ↥C.P.H0) = (d₁ : ℂ) := by
      have h1 : ClassFunction.restrict (Uin C) ν₁ (1 : ↥(Uin C)) = ν₁ (1 : ↥C.P.H0) :=
        ClassFunction.restrict_apply ..
      rw [← h1, hres₁]
      exact hd₁eq
    have hν₂1 : ν₂ (1 : ↥C.P.H0) = (d₂ : ℂ) := by
      have h1 : ClassFunction.restrict (Uin C) ν₂ (1 : ↥(Uin C)) = ν₂ (1 : ↥C.P.H0) :=
        ClassFunction.restrict_apply ..
      rw [← h1, hres₂]
      exact hd₂eq
    have heven : AlgIntModTwo (ν₁ (1 : ↥C.P.H0) + ν₂ (1 : ↥C.P.H0)) 0 := by
      rw [hν₁1, hν₂1]
      obtain ⟨k₁, hk₁⟩ := hodd₁
      obtain ⟨k₂, hk₂⟩ := hodd₂
      refine ⟨((k₁ + k₂ + 1 : ℕ) : ℂ), isIntegral_natCast _, ?_⟩
      rw [hk₁, hk₂]
      push_cast
      ring
    exact h24_1.trans (hred1.trans heven)
  -- **(6)** Gorenstein 4.2.10 on the fixed points
  have harith : ∀ u : ↥(Uin C),
      (∀ s ∈ (D.S : Subgroup G), s * ((u : ↥C.P.H0) : G) * s⁻¹ = ((u : ↥C.P.H0) : G)) →
      AlgIntModTwo (χ ((u : ↥C.P.H0) : G)) 0 :=
    fun u hcomm => lemma33Arith D C hDC hχ hEvenχ1 ((Subgroup.mem_subgroupOf).mp u.2) hcomm
  -- **(7)** Glauberman injectivity
  obtain ⟨u₀, hu₀⟩ := glaubCorrDistinct (S := ↥(D.S : Subgroup G)) (U := ↥(Uin C))
    (l33_isPGroup_S D) (l33_odd_card_Uin D C hDC) (l33_phiS D C hDC)
    a₁ a₂ ha₁irr ha₂irr hinv₁ hinv₂ hne_a
  -- **(8)** contradiction
  have hcomm₀ : ∀ s ∈ (D.S : Subgroup G),
      s * (((u₀ : ↥(Uin C)) : ↥C.P.H0) : G) * s⁻¹ = (((u₀ : ↥(Uin C)) : ↥C.P.H0) : G) :=
    (l33_mem_fixed' D C hDC (u₀ : ↥(Uin C))).mp u₀.2
  have hcong : AlgIntModTwo (ν₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0))
      (ν₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0)) := by
    have hsum := reduce (u₀ : ↥(Uin C)) hcomm₀
    have har := harith (u₀ : ↥(Uin C)) hcomm₀
    have h24u : AlgIntModTwo (χ (((u₀ : ↥(Uin C)) : ↥C.P.H0) : G))
        (∑ᶠ ν ∈ bset C f χ, ν ((u₀ : ↥(Uin C)) : ↥C.P.H0)) :=
      (lemma24 C f hf χ hχ).2.2 ((u₀ : ↥(Uin C)) : ↥C.P.H0)
        ((Subgroup.mem_subgroupOf).mp (u₀ : ↥(Uin C)).2)
    have h0 : AlgIntModTwo (ν₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0)
        + ν₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0)) 0 := hsum.symm.trans (h24u.symm.trans har)
    have h2 : AlgIntModTwo (2 * ν₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0)) 0 :=
      AlgIntModTwo.mul_two (isIntegral_apply_of_isIrreducibleCharacter' hν₂.1 _)
    have hdiff : AlgIntModTwo (ν₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0)
        - ν₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0)) 0 := by
      have h := h0.sub h2
      have heq : (ν₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0) + ν₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0))
          - 2 * ν₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0)
          = ν₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0) - ν₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0) := by ring
      rw [heq] at h
      simpa using h
    obtain ⟨c, hc, hceq⟩ := hdiff
    refine ⟨c, hc, ?_⟩
    have h' : ν₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0) - ν₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0) = 2 * c := by
      simpa using hceq
    simpa using h'
  have hcong_a : AlgIntModTwo (a₁ (u₀ : ↥(Uin C))) (a₂ (u₀ : ↥(Uin C))) := by
    have h1 : a₁ (u₀ : ↥(Uin C)) = ν₁ ((u₀ : ↥(Uin C)) : ↥C.P.H0) := by
      rw [← hres₁, ClassFunction.restrict_apply]
    have h2 : a₂ (u₀ : ↥(Uin C)) = ν₂ ((u₀ : ↥(Uin C)) : ↥C.P.H0) := by
      rw [← hres₂, ClassFunction.restrict_apply]
    rw [h1, h2]
    exact hcong
  exact hu₀ hcong_a

end Work.BG
