import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.lemma33Leaf
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.lemma24
import Submission.Work.BG.c3OrbitCard
import Submission.Work.BG.c3ValueBound
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.H0Conj

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G]

/-! ## The group-theoretic input of the `U = BK` case

In Bender–Glauberman's Theorem C the hypothesis on `U` is that it is the internal direct
product `U = (B₁ ⊓ K₂) × (B ⊔ (K₁ ⊓ K₂))`.  In the case `U = B ⊔ (K₁ ⊓ K₂)` (`BK = U`)
the element `t₁t₂` inverts the factor `B₁ ⊓ K₂` — which is then trivial — and centralizes
both `B` and `K₁ ⊓ K₂`; hence `t₁t₂` centralizes `U` and so does the whole cyclic group
`S₀ = ⟨t₁t₂⟩`.  This is the hypothesis `hcomm` of `c3OrbitCard`, which in turn is the only
extra input needed to force `𝒮(χ₁) = {κ}` in this case (the "Frobenius trigger" of BG p. 211:
`𝒮(χ₁) ≠ {κ₁} ⟹ [S₀,U] ≠ 1`). -/

/-- `x ∈ centralizer {y}` gives `x * y = y * x`. -/
theorem commute_of_mem_centralizer_singleton {X : Type} [Group X] {x y : X}
    (h : x ∈ Subgroup.centralizer ({y} : Set X)) : x * y = y * x :=
  (Subgroup.mem_centralizer_singleton_iff (g := y) (k := x)).mp h

/-- `t₁t₂` centralizes `U` when `U = B ⊔ (K₁ ⊓ K₂)`: it centralizes `B = C_U(S)` and
`K = K₁ ⊓ K₂` (inverted by both `t₁` and `t₂`). -/
theorem c3_gen_commutes (D : BGData G) (K1 K2 : Subgroup G)
    (h1 : IsMaxInverted D.H D.t1 K1) (h2 : IsMaxInverted D.H D.t2 K2)
    (hUBK : D.U = D.B ⊔ (K1 ⊓ K2)) :
    ∀ u : G, u ∈ D.U → (D.t1 * D.t2) * u = u * (D.t1 * D.t2) := by
  have hB1 : ∀ b ∈ D.B, b * D.t1 = D.t1 * b := by
    intro b hb
    exact commute_of_mem_centralizer_singleton
      (show b ∈ Subgroup.centralizer ({D.t1} : Set G) from
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).2)
  have hB2 : ∀ b ∈ D.B, b * D.t2 = D.t2 * b := by
    intro b hb
    exact commute_of_mem_centralizer_singleton
      (show b ∈ Subgroup.centralizer ({D.t2} : Set G) from
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).2).2)
  have hxB : D.B ≤ Subgroup.centralizer ({D.t1 * D.t2} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hb1 : b * D.t1 = D.t1 * b := hB1 b hb
    have hb2 : b * D.t2 = D.t2 * b := hB2 b hb
    calc b * (D.t1 * D.t2) = (b * D.t1) * D.t2 := by group
      _ = (D.t1 * b) * D.t2 := by rw [hb1]
      _ = D.t1 * (b * D.t2) := by group
      _ = D.t1 * (D.t2 * b) := by rw [hb2]
      _ = (D.t1 * D.t2) * b := by group
  have hxK : K1 ⊓ K2 ≤ Subgroup.centralizer ({D.t1 * D.t2} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk1 : D.t1 * k * D.t1⁻¹ = k⁻¹ := h1.2.2.1 k hk.1
    have hk2 : D.t2 * k * D.t2⁻¹ = k⁻¹ := h2.2.2.1 k hk.2
    have e2 : D.t2 * k = k⁻¹ * D.t2 := by
      calc D.t2 * k = (D.t2 * k * D.t2⁻¹) * D.t2 := by group
        _ = k⁻¹ * D.t2 := by rw [hk2]
    have f1 : D.t1 * k⁻¹ = k * D.t1 := by
      calc D.t1 * k⁻¹ = (D.t1 * k⁻¹ * D.t1⁻¹) * D.t1 := by group
        _ = (D.t1 * k * D.t1⁻¹)⁻¹ * D.t1 := by group
        _ = (k⁻¹)⁻¹ * D.t1 := by rw [hk1]
        _ = k * D.t1 := by group
    calc k * (D.t1 * D.t2) = (k * D.t1) * D.t2 := by group
      _ = (D.t1 * k⁻¹) * D.t2 := by rw [← f1]
      _ = D.t1 * (k⁻¹ * D.t2) := by group
      _ = D.t1 * (D.t2 * k) := by rw [← e2]
      _ = (D.t1 * D.t2) * k := by group
  have hxU : D.U ≤ Subgroup.centralizer ({D.t1 * D.t2} : Set G) := by
    rw [hUBK]
    exact sup_le hxB hxK
  intro u hu
  exact (commute_of_mem_centralizer_singleton (hxU hu)).symm

/-- In the `U = BK` case, `S₀ = ⟨t₁t₂⟩` centralizes `U`. -/
theorem c3_S0_commutes (D : BGData G) (K1 K2 : Subgroup G)
    (h1 : IsMaxInverted D.H D.t1 K1) (h2 : IsMaxInverted D.H D.t2 K2)
    (hUBK : D.U = D.B ⊔ (K1 ⊓ K2)) :
    ∀ x : G, x ∈ D.S0 → ∀ u : G, u ∈ D.U → x * u = u * x := by
  have hgen := c3_gen_commutes D K1 K2 h1 h2 hUBK
  intro x hx u hu
  have hle : Subgroup.zpowers (D.t1 * D.t2) ≤ Subgroup.centralizer (D.U : Set G) :=
    Subgroup.zpowers_le.mpr (by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (hgen u hu).symm)
  rw [D.gen] at hx
  exact ((Subgroup.mem_centralizer_iff (g := x) (s := (D.U : Set G))).mp (hle hx) u hu).symm

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **BG 1981, p. 211, (2)–(5) and the Frobenius trigger.**  Let `χ₁ ∈ ±Irr(G)` be a
constituent of `κ̃ = f κ` with multiplicity `1` (`(χ₁, f κ) = 1`), where `κ` is an admissible
`κ₁` (`IsKappa`).  Write `𝒮(χ₁) = bset C f χ₁` and `χ₁(t) = 1 + x`.

* `x ∈ ℤ` (the `κ`-term of Lemma 2.4 at `t` contributes `κ(t) = 1`, the remaining terms are
  `±ν(t) = ±ν(1)`);
* `|x| ≤ (|𝒮(χ₁)| - 1)|B|`;
* `x² ≤ 2|B|` when `|𝒮(χ₁)| ≤ 2`;
* `𝒮(χ₁) ≠ {κ} ⟹ U ≠ BK` (the Frobenius trigger).

The last clause is proved by contraposition: if `U = BK` then `S₀` centralizes `U`
(`c3_S0_commutes`), so every `ν ∈ Irr(H₀)` has `|Λν| = D.n` (`c3OrbitCard`); then any
`ν ∈ 𝒮(χ₁) \ {κ}` is either `s`-fixed — excluded by BG Lemma 3.3 (`lemma33Leaf`) together
with `4 ≤ D.n` — or not, in which case BG Lemma 3.4 (`lemma34Leaf`) would force
`𝒮(χ₁) = {ν, ν^s} ∌ κ`.  The first three clauses follow from BG Lemma 2.4 (`lemma24`) at
`t` together with the per-character value bound `c3ValueBound`. -/
theorem c3Bounds {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (K1 K2 : Subgroup G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.C3BoundsProp D C K1 K2 := by
  intro hC hThm hn hSec3 f hf κ hκ χ₁ hχ₁ hinner
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  obtain ⟨hmax1, hmax2, hdir, hcop, hB', hfrob⟩ := hThm
  have hThm' : ThmCHyps D K1 K2 := ⟨hmax1, hmax2, hdir, hcop, hB', hfrob⟩
  obtain ⟨hκirr, hκ1, hκsconj, hκS0, hκne⟩ := hκ
  have hκmem : κ ∈ bset C f χ₁ := ⟨hκirr, by rw [hinner]; norm_num⟩
  have hκt : κ C.t = 1 := hκS0 C.t (by rw [hC.t_eq]; exact D.t_mem)
  -- BG Lemma 2.4 at `t`
  obtain ⟨hbfin, hval, -⟩ := lemma24 C f hf χ₁ hχ₁
  have hvalt : χ₁ (C.t : G) =
      ∑ᶠ ν ∈ bset C f χ₁, ClassFunction.inner χ₁ (f ν) * ν C.t :=
    hval C.t C.t_not_mem_U
  -- the constituents of `𝒮(χ₁)` other than `κ`
  set F : Finset (ClassFunction ↥C.P.H0 ℂ) := hbfin.toFinset.erase κ with hF
  have hFmem : ∀ ν ∈ F, ν ∈ bset C f χ₁ ∧ ν ≠ κ := by
    intro ν hν
    exact ⟨(Set.Finite.mem_toFinset hbfin).mp (Finset.mem_of_mem_erase hν),
      (Finset.mem_erase.mp hν).1⟩
  -- the per-character value bound (BG p. 211, (3) and (5))
  have hmbound : ∀ ν ∈ F, ∃ m : ℤ, ν C.t = (m : ℂ) ∧ |m| ≤ (Nat.card D.B : ℤ) ∧
      ((bset C f χ₁).ncard ≤ 2 → m ^ 2 ≤ 2 * (Nat.card D.B : ℤ)) := by
    intro ν hν
    exact c3ValueBound D C K1 K2 hC hThm' hn hSec3 f hf κ
      ⟨hκirr, hκ1, hκsconj, hκS0, hκne⟩ χ₁ hχ₁ hinner ν (hFmem ν hν).1 (hFmem ν hν).2
  -- the Fourier coefficients at `ν ∈ F` are `±1` (coherence: `⟨f ν, f ν⟩ ≤ 2` and `f ν ∈ ZIrr`)
  have hsign : ∀ ν ∈ F, ClassFunction.inner χ₁ (f ν) = 1 ∨ ClassFunction.inner χ₁ (f ν) = -1 := by
    intro ν hν
    obtain ⟨hνbset, hνne⟩ := hFmem ν hν
    have hνirr : IsIrreducibleCharacter ν := hνbset.1
    have hkey : ν ∈ orbitKey C ν := Or.inl (s02c_LamEquiv_refl C ν)
    have hG := (hf.1 ν hνirr) ν hkey ν hkey hνirr hνirr
    have hnorm : ClassFunction.inner (f ν) (f ν) = 1 ∨ ClassFunction.inner (f ν) (f ν) = 2 := by
      by_cases hfix : sconj C ν = ν
      · right; rw [if_pos hfix] at hG; exact hG.2.2.1
      · left; rw [if_neg hfix] at hG; exact hG.2.2.1
    exact inner_pmIrr_eq_pm_one hG.1 hnorm hχ₁ hνbset.2
  -- the integer `x` and its sign decomposition
  set mf : ClassFunction ↥C.P.H0 ℂ → ℤ := fun ν =>
    if h : ν ∈ F then Classical.choose (hmbound ν h) else 0 with hmf
  set sf : ClassFunction ↥C.P.H0 ℂ → ℤ := fun ν =>
    if h : ν ∈ F then (if ClassFunction.inner χ₁ (f ν) = 1 then 1 else -1) else 0 with hsf
  have hmf_prop : ∀ ν ∈ F, ν C.t = (mf ν : ℂ) ∧ |mf ν| ≤ (Nat.card D.B : ℤ) ∧
      ((bset C f χ₁).ncard ≤ 2 → (mf ν) ^ 2 ≤ 2 * (Nat.card D.B : ℤ)) := by
    intro ν hν
    have hspec := Classical.choose_spec (hmbound ν hν)
    rw [hmf]
    simpa only [dif_pos hν] using hspec
  have hsf_prop : ∀ ν ∈ F, sf ν = 1 ∨ sf ν = -1 := by
    intro ν hν
    rcases hsign ν hν with h1 | h1
    · left; rw [hsf]; simp only [dif_pos hν, if_pos h1]
    · right; rw [hsf]; simp only [dif_pos hν]
      rw [if_neg (by rw [h1]; norm_num)]
  have hterm : ∀ ν ∈ F, ClassFunction.inner χ₁ (f ν) * ν C.t = ((sf ν * mf ν : ℤ) : ℂ) := by
    intro ν hν
    have hm := (hmf_prop ν hν).1
    rcases hsign ν hν with h1 | h1
    · have hs : sf ν = 1 := by rw [hsf]; simp only [dif_pos hν, if_pos h1]
      rw [hm, hs, h1]; push_cast; ring
    · have hs : sf ν = -1 := by
        rw [hsf]; simp only [dif_pos hν]
        rw [if_neg (by rw [h1]; norm_num)]
      rw [hm, hs, h1]; push_cast; ring
  set x : ℤ := ∑ ν ∈ F, sf ν * mf ν with hx
  have hFsum : ∑ ν ∈ F, ClassFunction.inner χ₁ (f ν) * ν C.t = ((x : ℤ) : ℂ) := by
    rw [hx, Finset.sum_congr rfl (fun ν hν => hterm ν hν)]
    push_cast
    rfl
  have hκmem' : κ ∈ hbfin.toFinset := (Set.Finite.mem_toFinset hbfin).mpr hκmem
  have hκnotF : κ ∉ F := by
    rw [hF]
    intro h
    exact (Finset.mem_erase.mp h).1 rfl
  have hκterm : ClassFunction.inner χ₁ (f κ) * κ C.t = 1 := by rw [hinner, hκt, one_mul]
  -- the value identity `χ₁(t) = 1 + x`
  have hxval : χ₁ (C.t : G) = 1 + (x : ℂ) := by
    rw [hvalt, finsum_mem_eq_finite_toFinset_sum _ hbfin, ← Finset.insert_erase hκmem',
      Finset.sum_insert hκnotF, hκterm, hFsum]
  have hcard_eq : F.card = (bset C f χ₁).ncard - 1 := by
    rw [hF, Finset.card_erase_of_mem hκmem', Set.ncard_eq_toFinset_card (bset C f χ₁) hbfin]
  -- `|x| ≤ (|𝒮(χ₁)| - 1)|B|`
  have hb4 : |x| ≤ ((bset C f χ₁).ncard - 1 : ℤ) * (Nat.card D.B : ℤ) := by
    have h1 : |x| ≤ ∑ ν ∈ F, |sf ν * mf ν| := by
      rw [hx]
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ ν ∈ F, |sf ν * mf ν| ≤ (Nat.card D.B : ℤ) := by
      intro ν hν
      have hs1 : |sf ν| = 1 := by
        rcases hsf_prop ν hν with h | h <;> rw [h] <;> norm_num
      rw [abs_mul, hs1, one_mul]
      exact (hmf_prop ν hν).2.1
    have h3 : ∑ _ν ∈ F, (Nat.card D.B : ℤ) = ((F.card : ℤ)) * (Nat.card D.B : ℤ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h4 : ((F.card : ℤ)) = ((bset C f χ₁).ncard - 1 : ℤ) := by
      have hle : 1 ≤ (bset C f χ₁).ncard := by
        have : 0 < (bset C f χ₁).ncard := (Set.ncard_pos hbfin).mpr ⟨κ, hκmem⟩
        omega
      rw [hcard_eq, Nat.cast_sub hle, Nat.cast_one]
    calc |x| ≤ ∑ ν ∈ F, |sf ν * mf ν| := h1
      _ ≤ ∑ _ν ∈ F, (Nat.card D.B : ℤ) := Finset.sum_le_sum h2
      _ = ((F.card : ℤ)) * (Nat.card D.B : ℤ) := h3
      _ = ((bset C f χ₁).ncard - 1 : ℤ) * (Nat.card D.B : ℤ) := by rw [h4]
  -- `x² ≤ 2|B|` when `|𝒮(χ₁)| ≤ 2`
  have hb5 : (bset C f χ₁).ncard ≤ 2 → x ^ 2 ≤ 2 * (Nat.card D.B : ℤ) := by
    intro hcard
    have hFcard : F.card ≤ 1 := by
      have hcard' : hbfin.toFinset.card ≤ 2 := by
        rwa [Set.ncard_eq_toFinset_card (bset C f χ₁) hbfin] at hcard
      have h := Finset.card_erase_of_mem hκmem'
      omega
    by_cases hF0 : F = ∅
    · have hx0 : x = 0 := by rw [hx, hF0, Finset.sum_empty]
      rw [hx0]; norm_num
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF0
      have hone : ∀ b ∈ F, ∀ c ∈ F, b = c := Finset.card_le_one.mp hFcard
      have hFs : F = {a} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, fun b hb => ?_⟩
        exact (hone b hb a ha)
      have hxa : x = sf a * mf a := by rw [hx, hFs, Finset.sum_singleton]
      rw [hxa]
      have hm : (mf a) ^ 2 ≤ 2 * (Nat.card D.B : ℤ) := (hmf_prop a ha).2.2 hcard
      have hs1 : sf a * sf a = 1 := by
        rcases hsf_prop a ha with h | h <;> rw [h] <;> norm_num
      calc (sf a * mf a) ^ 2 = (sf a * sf a) * (mf a) ^ 2 := by ring
        _ = (mf a) ^ 2 := by rw [hs1, one_mul]
        _ ≤ 2 * (Nat.card D.B : ℤ) := hm
  -- the Frobenius trigger: `U = BK` forces `𝒮(χ₁) = {κ}`
  have htrig : bset C f χ₁ ≠ {κ} → D.U ≠ D.B ⊔ (K1 ⊓ K2) := by
    intro hne hUBK
    have hcomm := c3_S0_commutes D K1 K2 hmax1 hmax2 hUBK
    have hsing : bset C f χ₁ = {κ} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hκmem, ?_⟩
      intro ν hν
      by_contra hne'
      have hνirr : IsIrreducibleCharacter ν := hν.1
      have hOrbν := c3OrbitCard D C hC hcomm ν hνirr
      have hOrbκ := c3OrbitCard D C hC hcomm κ hκirr
      by_cases hfix : sconj C ν = ν
      · -- BG Lemma 3.3: two `s`-fixed `ν` with `|Λν| = m` force `D.n = 2`
        have h33 := lemma33Leaf D C hC hSec3 f hf χ₁ hχ₁ ν hν κ hκmem hne' hfix hκsconj
          hOrbν hOrbκ
        obtain ⟨h2, -, -⟩ := h33
        omega
      · -- BG Lemma 3.4: a non-`s`-fixed `ν` with `|Λν| = m` forces `𝒮(χ₁) = {ν, ν^s}`
        have h34 := lemma34Leaf D C hC hSec3 f hf χ₁ hχ₁ ν hν hfix (Or.inr hOrbν)
        obtain ⟨hset, -⟩ := h34
        have hmem : κ = ν ∨ κ = sconj C ν := by
          rw [hset] at hκmem
          simpa using hκmem
        rcases hmem with h | h
        · exact hne' h.symm
        · have hconj := congrArg (sconj C) h
          rw [s02c_sconj_involutive, hκsconj] at hconj
          exact hne' hconj.symm
    exact hne hsing
  exact ⟨x, hxval, hb4, hb5, htrig⟩

end Work.BG
