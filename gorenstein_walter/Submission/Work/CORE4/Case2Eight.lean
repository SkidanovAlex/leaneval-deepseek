import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Layer
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.Case2EightIndex
import Submission.Work.CORE4.Case2EightExcept
import Submission.Work.CORE4.Case2EightP0LeP1
import Submission.Work.CORE4.Case2EightP1Le

namespace Work.CORE4

open Work.GW2 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

/-! ## §4 (8): the elementary conjuncts of `Case2EightFacts`

Only two conjuncts of `Case2EightFacts` are Bender's §4 (8) trichotomy on `Q = Ω₁(Z₂(O_p(U)))`
(namely `|U : B₀ K F(U)| ≤ p` and the exceptional clause `Case2InvNormal ∨ …`); they are proved in
the separate leaves `Case2EightIndex` and `Case2EightExcept`, and the object `A` in
`Case2EightObjExists`.  Everything else — `p ∣ |K₀|`, `A ≤ F ⊔ K₀`, `N_U(P) = U ⊓ M`,
`Odd p₀`, `p₀ ≤ p₁ ≤ p + 1`, `p₀ ≤ p` — is elementary and is proved here. -/

/-- `N_G(P) = M` for `P ≤ D.F` of prime order (Bender's §4 (11) first step), from the §4 (6)
TI-property: an element outside `M` would put `P` in `F ⊓ F^g = ⊥`. -/
theorem normalizerP_of_ctx6 (B : BenderSetup G) (C : Case2Ctx6 B) (P : Subgroup G)
    (hPF : P ≤ C.D.F) (hPne : P ≠ ⊥) : Subgroup.normalizer (P : Set G) = C.D.M := by
  apply le_antisymm
  · intro g hg
    by_contra hgm
    have hti := C.F_ti g hgm
    have hconj : conjSub g P = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hle : P ≤ C.D.F ⊓ conjSub g C.D.F := by
      refine le_inf hPF ?_
      rw [← hconj]; exact Subgroup.map_mono hPF
    rw [hti] at hle
    exact hPne (le_bot_iff.mp hle)
  · intro g hg
    rw [← Case2Pre.N_F B C.D C.pre] at hg
    have hconj : conjSub g P = P := conjSub_eq_self_of_le_cyclic C.F_cyclic hPF hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj

/-- §4 (8): `p ∣ |K₀|` for `p = |P|` prime with `P ≤ D.F`.  Indeed `p ∣ |F| ≤ |F(U)|`, and
§4 (7) says `π(K₀) = π(F(U))`. -/
theorem Case2Eight_dvd_K0 (B : BenderSetup G) (C : Case2Ctx6 B) (h7 : Case2SevenFacts B C.D)
    (p : ℕ) (P : Subgroup G) (hp : p.Prime) (hPF : P ≤ C.D.F) (hPcard : Nat.card P = p) :
    p ∣ Nat.card C.D.K0 := by
  have h7K0 : primesOf C.D.K0 = B.piFU := h7.2.1
  have hpFU : p ∈ primesOf C.D.K0 := by
    rw [h7K0]
    show p ∈ (Nat.card ↥(fittingIn B.U)).primeFactors
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, (Nat.card_pos (α := ↥(fittingIn B.U))).ne'⟩
    have h1 : p ∣ Nat.card ↥(C.D.F) := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    have h2 : Nat.card ↥(C.D.F) ∣ Nat.card ↥(fittingIn B.U) :=
      Subgroup.card_dvd_of_le (Case2Data.F_le_fitting B C.D)
    exact h1.trans h2
  exact (Nat.mem_primeFactors.mp hpFU).2.1

/-- §4 (8): `N_U(P) = U ⊓ M`. -/
theorem Case2Eight_NU (B : BenderSetup G) (C : Case2Ctx6 B) (P : Subgroup G)
    (hPF : P ≤ C.D.F) (hPne : P ≠ ⊥) :
    B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ C.D.M := by
  rw [normalizerP_of_ctx6 B C P hPF hPne]

/-- §4 (8): `N_U(P) ≤ N_G(A)` for the `(p,p)`-subgroup `A ≤ F ⊔ K`.  `A` is the unique subgroup
of `F ⊔ K` of order `p ^ 2` and exponent `p`, a property invariant under conjugation, while
`U ⊓ M` normalises both `F` (`N_G(F) = M`) and `K` (`K ⊴ U ⊓ M`). -/
theorem Case2Eight_le_normalizer_A (I : C4Inputs) (B : BenderSetup G) (C : Case2Ctx6 B)
    (p : ℕ) (P A : Subgroup G) (hobj : Case2EightObj C.D p P A) :
    B.U ⊓ C.D.M ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  obtain ⟨-, hgM⟩ := Subgroup.mem_inf.mp hg
  have hgNF : g ∈ Subgroup.normalizer (C.D.F : Set G) := by
    rw [Case2Pre.N_F B C.D C.pre]; exact hgM
  have hFs : C.D.F.map ((MulAut.conj g).toMonoidHom) = C.D.F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgNF
  have hKle : C.D.K ≤ B.U ⊓ C.D.M := Case2Data.K_le B C.D
  have hKn := Case2Data.K_normal_in_UinfM I B C.D
  have key : ∀ a b : G, a ∈ C.D.K → b ∈ (B.U ⊓ C.D.M) → b * a * b⁻¹ ∈ C.D.K :=
    (Subgroup.normal_subgroupOf_iff hKle).mp hKn
  have hgNK : g ∈ Subgroup.normalizer (C.D.K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk; exact key k g hk hg
    · intro hk
      have h := key (g * k * g⁻¹) g⁻¹ hk (Subgroup.inv_mem _ hg)
      have heq : g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k := by group
      rwa [heq] at h
  have hKs : C.D.K.map ((MulAut.conj g).toMonoidHom) = C.D.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgNK
  have hFK : (C.D.F ⊔ C.D.K).map ((MulAut.conj g).toMonoidHom) = C.D.F ⊔ C.D.K := by
    rw [Subgroup.map_sup, hFs, hKs]
  have hAle : conjSub g A ≤ C.D.F ⊔ C.D.K := by
    have hm := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hobj.2.2.2.1
    rwa [hFK] at hm
  have hcard : Nat.card ↥(conjSub g A) = p ^ 2 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hobj.2.2.2.2.1
  have hexp : ∀ x ∈ conjSub g A, x ^ p = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hobj.2.2.2.2.2.1 a ha, map_one]
  have huniq := hobj.2.2.2.2.2.2.2 (conjSub g A) hAle hcard hexp
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact huniq

/-- §4 (8): `p₀ = |N_U(A) : N_U(P)|` is odd (`|U|` is odd). -/
theorem Case2Eight_odd_p0 (B : BenderSetup G) (_p : ℕ) (P A : Subgroup G)
    (_h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G)) :
    Odd (Case2EightP0 B P A) := by
  unfold Case2EightP0
  have hdvd := Subgroup.relIndex_dvd_card (B.U ⊓ Subgroup.normalizer (P : Set G))
    (B.U ⊓ Subgroup.normalizer (A : Set G))
  have hdvd2 : Nat.card ↥(B.U ⊓ Subgroup.normalizer (A : Set G)) ∣ Nat.card ↥B.U :=
    Subgroup.card_dvd_of_le inf_le_left
  exact Odd.of_dvd_nat B.U_odd (hdvd.trans hdvd2)

/-- §4 (8): `p₀ ≤ p`, from `p₀` odd and `p₀ ≤ p₁ ≤ p + 1`. -/
theorem Case2Eight_p0_le_p (B : BenderSetup G) (p : ℕ) (P A : Subgroup G)
    (hp0odd : Odd (Case2EightP0 B P A))
    (h6a : Case2EightP0 B P A ≤ Case2EightP1 P A) (h6b : Case2EightP1 P A ≤ p + 1)
    (hpodd : Odd p) : Case2EightP0 B P A ≤ p := by
  have hp1 : Case2EightP0 B P A ≤ p + 1 := le_trans h6a h6b
  obtain ⟨k, hk⟩ := hpodd
  have hp1e : Even (p + 1) := ⟨k + 1, by rw [hk]; ring⟩
  have hne : Case2EightP0 B P A ≠ p + 1 := by
    intro h
    rw [h] at hp0odd
    exact (Nat.not_even_iff_odd.mpr hp0odd) hp1e
  exact Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hp1 hne)

/-- `A` is abelian: `A ≤ F ⊔ K`, and `F ⊔ K` is the direct product of the commuting abelian
groups `F` and `K` (both cyclic). -/
theorem Case2Eight_A_comm (I : C4Inputs) (B : BenderSetup G) (C : Case2Ctx6 B)
    (A : Subgroup G) (hAle : A ≤ C.D.F ⊔ C.D.K) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  have hN : C.D.F ≤ Subgroup.normalizer (C.D.K : Set G) := F_le_normalizer_K_c4 I B C.D
  have hcoe : (↑(C.D.F ⊔ C.D.K) : Set G) = (↑C.D.F : Set G) * (↑C.D.K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right C.D.F C.D.K hN
  have hcyclic : ∀ (H : Subgroup G), IsCyclic ↥H → ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    intro H hH a ha b hb
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥H)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
    have ham : a = (g : G) ^ m := by
      have h := congrArg (Subgroup.subtype H) (hm.symm : (⟨a, ha⟩ : ↥H) = g ^ m)
      simpa using h
    have hbn : b = (g : G) ^ n := by
      have h := congrArg (Subgroup.subtype H) (hn.symm : (⟨b, hb⟩ : ↥H) = g ^ n)
      simpa using h
    rw [ham, hbn, ← zpow_add, add_comm, zpow_add]
  intro x hx y hy
  have hx' : x ∈ ((↑C.D.F : Set G) * (↑C.D.K : Set G)) := by rw [← hcoe]; exact hAle hx
  have hy' : y ∈ ((↑C.D.F : Set G) * (↑C.D.K : Set G)) := by rw [← hcoe]; exact hAle hy
  obtain ⟨f1, hf1, k1, hk1, hxeq⟩ := Set.mem_mul.mp hx'
  obtain ⟨f2, hf2, k2, hk2, hyeq⟩ := Set.mem_mul.mp hy'
  rw [← hxeq, ← hyeq]
  have hc1 : k1 * f2 = f2 * k1 := (F_commute_K_c4 I B C.D C.pre f2 hf2 k1 hk1).symm
  have hc2 : k2 * f1 = f1 * k2 := (F_commute_K_c4 I B C.D C.pre f1 hf1 k2 hk2).symm
  have hF : f1 * f2 = f2 * f1 := hcyclic C.D.F C.F_cyclic f1 hf1 f2 hf2
  have hK : k1 * k2 = k2 * k1 := hcyclic C.D.K C.pre.K_cyclic k1 hk1 k2 hk2
  calc f1 * k1 * (f2 * k2) = f1 * (k1 * f2) * k2 := by group
    _ = f1 * (f2 * k1) * k2 := by rw [hc1]
    _ = (f1 * f2) * (k1 * k2) := by group
    _ = (f2 * f1) * (k2 * k1) := by rw [hF, hK]
    _ = f2 * f1 * (k2 * k1) := by group
    _ = f2 * (f1 * k2) * k1 := by group
    _ = f2 * (k2 * f1) * k1 := by rw [← hc2]
    _ = f2 * k2 * (f1 * k1) := by group

/-- Bender 1981, §4 (8) (pp. 225–226), design-pass-9 layer.

Statement: `Case2EightImpl I`, i.e. for `BenderCtx G`, `B` with `Case2 B`, `C : Case2Ctx6 B`, and
the data `Case2PrePlus B C.D` and `Case2SevenFacts B C.D` (§4 (1)–(7)), produce `Case2EightAll B C.D`:
for every prime `p` and every `P ≤ D.F` with `|P| = p`, there is `A` with

    Case2EightObj D p P A  =  p prime, P ≤ D.F, |P| = p, A ≤ D.F ⊔ D.K, |A| = p²,
                              ∀ x ∈ A, x^p = 1, P ≤ A, and A is the UNIQUE such subgroup of
                              D.F ⊔ D.K
    Case2EightFacts B D p P A  =  p ∣ |K₀| ∧ A ≤ D.F ⊔ K₀ ∧ N_U(P) = U ∩ M ∧ N_U(P) ≤ N_G(A) ∧
                              Odd p₀ ∧ p₀ ≤ p₁ ≤ p+1 ∧ p₀ ≤ p ∧
                              |U : B₀ K F(U)| ≤ p ∧
                              (Case2InvNormal B D ∨ (u ≤ p ∧ A ⊴ F(U) ∧ (¬ U ≤ M → 3 ≤ p₀)))

where `p₀ = Case2EightP0 B P A = |N_U(A) : N_U(P)|`, `p₁ = Case2EightP1 P A` = number of
`G`-conjugates of `P` inside `A`, `u = Case2EightU B A = |U : N_U(A)|`, and the exceptional clause
`Case2InvNormal B D` is `I_U(s) ⊲ Ĥ` — the design-pass-9 reading of the printed exception.

The object `A` and the two §4 (8) trichotomy conjuncts are proved in
`Submission.Work.CORE4.Case2EightObjExists`, `.Case2EightIndex` and `.Case2EightExcept`; the
remaining conjuncts are proved in this file. -/
theorem Case2Eight (I : Work.GW2.C4Inputs) : Work.GW2.Case2EightImpl I := by
  intro G _ _ hbc B h2 C hplus h7 p P hp hPF hPcard
  obtain ⟨A, hobj⟩ := Case2EightObjExists I G hbc B h2 C hplus h7 p P hp hPF hPcard
  have hAle : A ≤ C.D.F ⊔ C.D.K := hobj.2.2.2.1
  have hPA : P ≤ A := hobj.2.2.2.2.2.2.1
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ C.D.M :=
    Case2Eight_NU B C P hPF hpne
  have h4 : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNU]; exact Case2Eight_le_normalizer_A I B C p P A hobj
  have hp0odd : Odd (Case2EightP0 B P A) := Case2Eight_odd_p0 B p P A h4
  have h6a : Case2EightP0 B P A ≤ Case2EightP1 P A := Case2EightP0LeP1 B p P A hPA h4
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := Case2Eight_A_comm I B C A hAle
  have h6b : Case2EightP1 P A ≤ p + 1 :=
    Case2EightP1Le p P A hp hPA hobj.2.2.2.2.1 hobj.2.2.2.2.2.1 hAcomm hPcard
  have hpodd : Odd p := by
    have h1 : p ∣ Nat.card ↥C.D.F := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    exact Odd.of_dvd_nat B.U_odd (h1.trans (Subgroup.card_dvd_of_le (Case2Data.F_le_U B C.D)))
  exact ⟨A, hobj,
    Case2Eight_dvd_K0 B C h7 p P hp hPF hPcard,
    Case2EightA_le_FsupK0 I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj,
    hNU, h4, hp0odd, h6a, h6b,
    Case2Eight_p0_le_p B p P A hp0odd h6a h6b hpodd,
    Case2EightIndex I G hbc B h2 C hplus h7 p P hp hPF hPcard,
    Case2EightExcept I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj⟩

end Work.CORE4
