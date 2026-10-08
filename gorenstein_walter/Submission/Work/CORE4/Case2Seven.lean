import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Layer
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2SevenAux

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The two pieces of the equality `π(K₀) = π(F(U))`

Bender's §4 (7) contains the chain

    π(K F(M) [S∩M, B]) = π(C_U(K₀F)) = π = π(K₀),      π := π(F(U)),   K₀ := F(U) ∩ K.

The equality `π = π(K₀)` has two ingredients, and the lemmas of this section separate them
completely:

* `π(F(U)) = π(K₀F)` — the "`X`-argument" of Bender p. 225: for a prime `r ∉ π(K₀F)`, the
  `r`-subgroup `O_r(F(U))` of the nilpotent group `F(U)` centralizes `X` (every element of
  `X ≤ K₀F` has order coprime to `r`), hence lies in `N_G(X) ≤ M`, hence in
  `F(U) ∩ M = K₀F`, hence is trivial.  This is the only place in §4 (7) where the input `X`
  of `Case2 B` (with `N_G(X) ≤ M`) is used.
* `π(F) ⊆ π(K₀)` — Bender derives this in the paragraph of (6) from the witness
  `∃ g ∉ M, F^g ≤ K₁F = F(U) ∩ M`; then `F ≅ F^g ≅ F^gF/F ≤ K₁F/F ≅ K₁/(K₁ ∩ F)`, so
  `|F| ∣ |K₁|` and `π(F) ⊆ π(K₁) = π(K₀)`.

`conj2_iff_piF` below is the machine-checked form of the separation: **given** the first
ingredient (`hFU : B.piFU = primesOf (D.K0 ⊔ D.F)`), the second conjunct of `Case2SevenFacts`
is *equivalent* to `π(F) ⊆ π(K₀)`. -/

/-- Bender §4 (3) (`SixThree`), oriented towards `K₀ = F(U) ∩ K`: `F(U) ∩ M = K₀ ⊔ F`. -/
theorem K0_sup_F_eq (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D) :
    D.K0 ⊔ D.F = Work.GW2.fittingIn B.U ⊓ D.M :=
  (SixThree I G hbc B D hpre).symm

/-- `K₀ ⊓ F = 1`: `K₀ ⊆ K = I_{U∩M}(s)` is inverted by `s`, while `F ⊆ B₀ = C_U(s)` is fixed
by `s`; an element of `K₀ ⊓ F` is therefore its own inverse, and `U` has odd order. -/
theorem K0_inf_F_eq_bot (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) :
    D.K0 ⊓ D.F = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxK0, hxF⟩ := Subgroup.mem_inf.mp hx
  have hxK : x ∈ D.K := hxK0.2
  have hxinv : D.s * x * D.s⁻¹ = x⁻¹ := D.K_inv B x hxK
  have hxB0 : x ∈ D.B0 := D.F_le_B0 B hxF
  have hxcen : x ∈ Subgroup.centralizer ({D.s} : Set G) := by
    rw [D.B0_def] at hxB0
    exact (Subgroup.mem_inf.mp hxB0).2
  have hxs : D.s * x = x * D.s :=
    (Subgroup.mem_centralizer_iff.mp hxcen) D.s (Set.mem_singleton D.s)
  have hconj : D.s * x * D.s⁻¹ = x := by rw [hxs, mul_assoc, mul_inv_cancel, mul_one]
  have hxeq : x = x⁻¹ := by
    calc x = D.s * x * D.s⁻¹ := hconj.symm
      _ = x⁻¹ := hxinv
  have hxx : x * x = 1 := by
    have h2 : x * x = x * x⁻¹ := congrArg (fun y => x * y) hxeq
    rwa [mul_inv_cancel] at h2
  have hdvd2 : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hxx
  have hdvdU : orderOf x ∣ Nat.card ↥B.U := Subgroup.orderOf_dvd_natCard B.U (D.F_le_U B hxF)
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat B.U_odd hdvdU
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h)
  · rw [h] at hodd
    exact absurd hodd (by decide)

/-- `K₀ ⊴ K₀ ⊔ F`: `K₀ = F(U) ∩ K` with `K ⊴ U ∩ M` (Bender 1.5(iii), `Case2SevenAux`) and
`F(U) ⊴ H`; every element of `K₀ ⊔ F = F(U) ∩ M` lies in `F(U) ∩ M ⊆ U ∩ M`. -/
theorem K0_normal_in_K0supF (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D) :
    (D.K0.subgroupOf (D.K0 ⊔ D.F)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff le_sup_left]
  intro a b ha hb
  have hb' : b ∈ Work.GW2.fittingIn B.U ⊓ D.M := by
    rw [← K0_sup_F_eq I hbc B D hpre]
    exact hb
  obtain ⟨hbU, hbM⟩ := Subgroup.mem_inf.mp hb'
  have ha' : a ∈ Work.GW2.fittingIn B.U ⊓ D.K := ha
  obtain ⟨haU, haK⟩ := Subgroup.mem_inf.mp ha'
  have hbU' : b ∈ B.U := Subgroup.map_subtype_le _ hbU
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Work.GW2.fittingIn B.U).mul_mem
      ((Work.GW2.fittingIn B.U).mul_mem hbU haU) ((Work.GW2.fittingIn B.U).inv_mem hbU)
  · exact (Subgroup.normal_subgroupOf_iff (D.K_le B)).mp (Case2Data.K_normal_in_UinfM I B D)
      a b haK (Subgroup.mem_inf.mpr ⟨hbU', hbM⟩)

/-- `|K₀ ⊔ F| = |K₀| · |F|` (again `K₀ ⊓ F = 1` and `K₀ ⊴ K₀ ⊔ F`). -/
theorem card_K0_sup_F (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D) :
    Nat.card ↥(D.K0 ⊔ D.F) = Nat.card ↥D.K0 * Nat.card ↥D.F := by
  have hrel := relIndex_eq_card_of_sup_eq_inf_eq_bot D.K0 D.F (D.K0 ⊔ D.F)
    le_sup_left le_sup_right rfl (K0_inf_F_eq_bot B D) (K0_normal_in_K0supF I hbc B D hpre)
  have hmul := Subgroup.relIndex_mul_card D.K0 (D.K0 ⊔ D.F)
  rw [inf_eq_left.mpr le_sup_left] at hmul
  rw [hrel] at hmul
  rw [← hmul, mul_comm]

/-- `π(A ⊔ B) = π(A) ∪ π(B)` when `|A ⊔ B| = |A| · |B|`. -/
theorem primesOf_sup_of_card (A B : Subgroup G)
    (h : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B) :
    primesOf (A ⊔ B) = primesOf A ∪ primesOf B := by
  ext p
  rw [primesOf, primesOf, primesOf, h]
  simp only [Set.mem_setOf_eq, Set.mem_union, Nat.mem_primeFactors]
  have hA : Nat.card ↥A ≠ 0 := Nat.card_pos.ne'
  have hB : Nat.card ↥B ≠ 0 := Nat.card_pos.ne'
  constructor
  · rintro ⟨hp, hdvd, -⟩
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h' | h'
    · exact Or.inl ⟨hp, h', hA⟩
    · exact Or.inr ⟨hp, h', hB⟩
  · rintro (⟨hp, hdvd, -⟩ | ⟨hp, hdvd, -⟩)
    · exact ⟨hp, hdvd.trans (Nat.dvd_mul_right _ _), mul_ne_zero hA hB⟩
    · exact ⟨hp, hdvd.trans (Nat.dvd_mul_left _ _), mul_ne_zero hA hB⟩

/-- **The reduction of the second conjunct of §4 (7).**  Granting Bender's `X`-argument
`π(F(U)) = π(K₀F)` (`hFU`), the assertion `π(K₀) = π(F(U))` is *equivalent* to
`π(F) ⊆ π(K₀)` — the statement Bender obtains from the witness `∃ g ∉ M, F^g ≤ K₁F`. -/
theorem conj2_iff_piF (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D)
    (hFU : B.piFU = primesOf (D.K0 ⊔ D.F)) :
    (primesOf D.K0 = B.piFU) ↔ primesOf D.F ⊆ primesOf D.K0 := by
  have hsplit : primesOf (D.K0 ⊔ D.F) = primesOf D.K0 ∪ primesOf D.F :=
    primesOf_sup_of_card _ _ (card_K0_sup_F I hbc B D hpre)
  have hK0le : primesOf D.K0 ⊆ B.piFU := by
    rw [hFU, hsplit]
    exact Set.subset_union_left
  constructor
  · intro h p hp
    have h1 : p ∈ primesOf (D.K0 ⊔ D.F) := by
      rw [hsplit]
      exact Or.inr hp
    rw [← hFU] at h1
    rw [← h] at h1
    exact h1
  · intro h
    refine le_antisymm hK0le ?_
    rw [hFU, hsplit]
    exact Set.union_subset le_rfl h

/-- Consequence: the second conjunct of `Case2SevenFacts` *fails* whenever `K₀ = ⊥` (and
`F ≠ ⊥`, which `Case2Pre` provides).  So the leaf needs a hypothesis forcing `K₀ ≠ ⊥` —
Bender's `K₁ ≠ 1`, which he reads off the structure of `E(M)/Z(E) ∈ {A₇, L₂(q)}`. -/
theorem conj2_fails_of_K0_eq_bot (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D)
    (hFU : B.piFU = primesOf (D.K0 ⊔ D.F)) (hbot : D.K0 = ⊥) :
    primesOf D.K0 ≠ B.piFU := by
  intro h
  have hle : primesOf D.F ⊆ primesOf D.K0 :=
    (conj2_iff_piF I hbc B D hpre hFU).mp h
  have hF1 : Nat.card ↥D.F = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpF : p ∈ primesOf D.F := by
      rw [primesOf]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.card_pos.ne'⟩
    have hpk : p ∈ primesOf D.K0 := hle hpF
    rw [hbot] at hpk
    rw [primesOf, (Subgroup.card_eq_one (H := (⊥ : Subgroup G))).mpr rfl,
      Nat.primeFactors_one] at hpk
    exact absurd hpk (by simp)
  exact Case2Pre.F_ne B D hpre ((Subgroup.card_eq_one (H := D.F)).mp hF1)

/-- Bender 1981, §4 (7) (p. 225), design-pass-9 layer.

Statement: `Case2SevenImpl I`, i.e. for `BenderCtx G`, `B : BenderSetup G` with `Case2 B`, and the
data `C : Case2Ctx6 B` (§4 (1)–(6)) together with `Case2PrePlus B C.D` (Bender's Sylow choice
`S ∩ M ∈ Syl₂(M)` and (1),(2)), produce

    Case2SevenFacts B C.D   =   O₂(H∩M) = O₂(H)   ∧   π(K₀) = π(F(U)) =
                                π(U ∩ C_U(K₀F))   ∧   π(K) ⊆ π   ∧   π(F(M)) ⊆ π   ∧
                                π([S∩M, B₀]) ⊆ π,

with `K₀ = D.K0 = F(U) ∩ K`, `π = B.piFU = π(F(U))`, `B₀ = D.B0 = C_{U∩M}(S ∩ E)`.
NOTE (design pass 9, settled from the 500-dpi page image): it is `C_U(K₀F)`, not `C_H(K₀F)`; all
statements are `≤`/equal as printed, never `<`.

Route (Bender p. 225): `K ⊴ H ∩ M` by (1) and the Sylow choice, and `F`, `K₀` are cyclic and
normal in `H ∩ M`, so `(H ∩ M)'` centralizes `K₀F`.
* By 1.1(iv) (`I.toolkit.c11iv`, `Coprime11ivProp`) every `π'`-subgroup of `H` centralizing
  `K₀F = N_{F(U)}(F)` lies in `C_H(F(U)) = O₂(H) × Z(F(U))`.
* `O₂(H ∩ M) ≤ O₂(H)` follows; `O₂(H) ≤ C_H(F(U)) ≤ N_G(X) ≤ M` (with `X` from `Case2 B`) gives the
  reverse inclusion.
* `π(K₀) = π`: for `r ∈ π ∖ π(K₀F)`, `O_r(F(U))` centralizes `X ≤ K₀F`, hence lies in `M`, hence
  in `F(U) ∩ M = K₀F`, hence is trivial; then `π(F) ⊆ π(K₀)` by (6).
* `F(M)` is odd (`O₂(M)` centralizes the dihedral `S ∩ E`) and `F(M) ≤ C_M(E) ≤ H ∩ M`, so
  `F(M) ≤ O(H ∩ M) = U ∩ M`; its `π'`-part centralizes `F` and `K₀`, so lies in `C_U(K₀F)`, a
  `π`-group.
* `K, [S ∩ M, B₀] ≤ (H ∩ M)' ∩ U ≤ C_U(K₀F)`.

Useful: `Submission.Work.CORE4.Case2SevenAux` (in the area) already has `K ⊴ U ⊓ M` and
`F(X) ⊴ X`; `Submission.Work.CORE4.CountSetup` has `M = E·C_M(t)`, `N_G(E(M)) = M`.

## Gap (analysis of this file; see `conj2_iff_piF` and `conj2_fails_of_K0_eq_bot` above)

The statement is **not** derivable from the stated hypotheses.  Step 4 of the route,
`π(F) ⊆ π(K₀)` "by (6)", is Bender's (6)-*paragraph* argument, which needs the witness
`∃ g ∈ N_G(F(U) ∩ M) ∖ M` (so that `F^g ≤ F(U) ∩ M = K₁F`, whence `|F| ∣ |K₁|`).  That witness is
not among the hypotheses: `Case2Ctx6` formalises (6) as `F ∧ F^g = 1` + `IsCyclic F`, and the
design's own delegation of the witness (`Submission.Work.CORE4.SixConj`) was reported
under-hypothesised because it forces `K ≠ ⊥`, Bender's `K ≠ 1` coming from the structure of
`E(M)/Z(E) ∈ {A₇, L₂(q)}` (§4 (1)) rather than from the `(1)`–`(6)` data.

Machine-checked consequence: granting step 3 (the `X`-argument `π(F(U)) = π(K₀F)`, `hFU`), the
conjunct `π(K₀) = π(F(U))` is *equivalent* to `π(F) ⊆ π(K₀)` (`conj2_iff_piF`), and it *fails*
whenever `K₀ = ⊥` (`conj2_fails_of_K0_eq_bot`) — and `K = ⊥` (equivalently `s` centralises
`U ∩ M`, so that `B₀ = U ∩ M`, `F = F(U) ∩ M ≠ ⊥`) is compatible with every conjunct of
`Case2Data`, `Case2Pre`, `Case2PrePlus` and `Case2Ctx6`.

Fix: add to `Case2PrePlus` (or to this leaf's hypotheses) Bender's witness
`∃ g : G, g ∉ D.M ∧ conjSub g D.F ≤ fittingIn B.U ⊓ D.M` — equivalently, given `F ≠ 1`, the
statement `K₁ = F(U) ∩ K ≠ ⊥`, which is what Bender's §4 (1) supplies. -/
theorem Case2Seven (I : Work.GW2.C4Inputs) : Work.GW2.Case2SevenImpl I := by sorry

end Work.CORE4
