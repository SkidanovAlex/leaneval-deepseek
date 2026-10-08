/-
Area BG (Bender–Glauberman 1981): `Work.GW2.C16.KNeOneProp` (Remark 3.5, design leaf G8).

This is the version of the proof prescribed by design pass 26 (`NOTES_LEAD_gw_design26.md`,
`_design_gw/Core26.lean`): `KNeOneProp` is derived from Bender–Glauberman's **Theorem B**
(`Work.GW2.BGThmBProp`) and the centralizer splitting `C_G(t) = U · S`
(`Work.GW2.CentralizerSplitProp`), with no other input.

Route (BG p. 210, "If `U = B`, then `G₁ := N_G(B)` is as in Theorem B"):

* `K = K₁ ⊓ K₂ = ⊥` forces `D.U = D.B` (the Frobenius clause with `K = ⊥` is absurd), and then
  `D.B = D.U ≤ C_G(D.S)` (`B_eq_inf_centralizer_S`), i.e. `S` centralizes `U`.
* With `H = U ⊔ S`, every involution of `N := N_G(U)` is `N`-conjugate into `S` (Sylow), and for
  an involution `x = c t c⁻¹ ∈ S` the odd-order group `U` lies in `C(x) = U^c ⊔ S^c` with `S^c` a
  `2`-group normalizing `U^c`; hence `U ≤ U^c`, `|U| < ∞`, so `U = U^c` and `c ∈ N`.  Thus `N` has
  one class of involutions (and `N ≠ ⊤`, `D.H ≤ N`).
* Theorem B gives `|G : N| = 5`; `G` simple makes `G ↪ Sym(G/N)` injective, so `|G| ∣ 120` and
  `|N| ∣ 24`; `|U|` is odd, `> 1` and divides `|N|`, so `|U| = 3` and `U` is a Sylow `3`-subgroup
  with `n₃ = |G : N_G(U)| = 5 ≢ 1 (mod 3)` — contradiction.

The general statement "an odd-order element centralizing a Sylow `2`-subgroup lies in `O_{2'}(G)`"
is **false** (`G = PSL(2,27):3`, `O(G) = 1`, `C_G(S) ≅ C₆ × C₂`), which is why the one-class step
above is done directly; see `NOTES_LEAD_gw_design26.md` §1.  Consequently the unconditional
`KNeOneProp` is not available in this workspace, and `kNeOne` below carries exactly the two
hypotheses that design pass 26 prescribes (`BGThmBProp` and `CentralizerSplitProp`).
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.S_le_H
import Submission.Work.BG.B_eq_inf_centralizer_S
import Submission.Work.GLUE.Bridge
import Submission.Work.GLUE.InBridge

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

/-! ## 1. Odd subgroups of `M ⊔ P` (`P` a 2-group normalizing `M`) lie in `M` -/

/-- An odd-order subgroup of a group `U ⊔ S` with `U` normal and `S` a `2`-group lies in `U`. -/
theorem le_of_sup_isPGroup' {G : Type*} [Group G] [Finite G] {U S X : Subgroup G}
    [U.Normal] (hUS : U ⊔ S = ⊤) (hS : IsPGroup 2 S) (hX : Odd (Nat.card X)) : X ≤ U := by
  have h1 : U.relIndex X ∣ U.index := Subgroup.relIndex_dvd_index_of_normal U X
  have hidx : U.index = U.relIndex S := by
    rw [← Subgroup.relIndex_top_right, ← hUS, Subgroup.relIndex_sup_left]
  have h3 : U.relIndex X ∣ Nat.card S := (hidx ▸ h1).trans (Subgroup.relIndex_dvd_card U S)
  have h4 : U.relIndex X ∣ Nat.card X := Subgroup.relIndex_dvd_card U X
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hS
  have h5 : U.relIndex X ∣ 2 ^ n := hn ▸ h3
  have hnot : ¬ 2 ∣ Nat.card X := by
    rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hX
  have hcop : Nat.Coprime (2 ^ n) (Nat.card X) :=
    (Nat.prime_two.coprime_pow_of_not_dvd (m := n) hnot).symm
  exact Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop h5 h4)

theorem le_of_le_sup_of_odd {G : Type} [Group G] [Finite G] {M P X : Subgroup G}
    (hPM : P ≤ normalizer (M : Set G)) (hP : IsPGroup 2 P) (hX : Odd (Nat.card X))
    (hle : X ≤ M ⊔ P) : X ≤ M := by
  set Y := M ⊔ P with hY
  have hMY : M ≤ Y := le_sup_left
  have hPY : P ≤ Y := le_sup_right
  have hYN : Y ≤ normalizer (M : Set G) := sup_le Subgroup.le_normalizer hPM
  have hMn : (M.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMY).mpr hYN
  have htop : M.subgroupOf Y ⊔ P.subgroupOf Y = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hMY hPY, Subgroup.subgroupOf_self]
  have hP' : IsPGroup 2 (P.subgroupOf Y) := hP.comap_subtype
  have hX' : Odd (Nat.card (X.subgroupOf Y)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  have hle' := le_of_sup_isPGroup' htop hP' hX'
  intro x hx
  have hxY : x ∈ Y := hle hx
  have hmem : (⟨x, hxY⟩ : Y) ∈ M.subgroupOf Y :=
    hle' (by simpa [Subgroup.mem_subgroupOf] using hx)
  simpa [Subgroup.mem_subgroupOf] using hmem

/-! ## 2. One class of involutions in `N_G(U)` when `S` centralizes `U` (BG Remark 3.5) -/

section OneClass

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
/-- `U ≤ C_G(S)` makes `S ≤ N_G(U)`. -/
theorem le_normalizer_of_le_centralizer {U S : Subgroup G}
    (hcent : U ≤ centralizer (S : Set G)) : S ≤ normalizer (U : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hc : s * h = h * s := (mem_centralizer_iff.mp (hcent hh)) s hs
    have : s * h * s⁻¹ = h := by rw [hc, mul_inv_cancel_right]
    rw [this]; exact hh
  · intro hh
    have hc : s * (s * h * s⁻¹) = (s * h * s⁻¹) * s :=
      (mem_centralizer_iff.mp (hcent hh)) s hs
    have : s * h * s⁻¹ = h := by
      have h2 : s * (s * h * s⁻¹) = s * h := by rw [hc, inv_mul_cancel_right]
      exact mul_left_cancel h2
    rw [this] at hh; exact hh

/-- **Fusion step.** With `H = U ⊔ S` (`CentralizerSplitProp`) and `S` centralizing `U`,
every involution `x ∈ S` is `N_G(U)`-conjugate to `t`.  If `x = c t c⁻¹`, then
`U ≤ C(x) = U^c ⊔ S^c`, `S^c` is a `2`-group normalizing `U^c` and `|U|` is odd, so `U ≤ U^c`,
hence `U = U^c`, i.e. `c ∈ N_G(U)`. -/
theorem conj_t_of_mem_S (D : BGData G) (hUS : D.U ⊔ (D.S : Subgroup G) = D.H)
    (hcent : D.U ≤ centralizer ((D.S : Subgroup G) : Set G)) (hUodd : Odd (Nat.card D.U))
    {x : G} (hxS : x ∈ (D.S : Subgroup G)) (hx : orderOf x = 2) :
    ∃ c ∈ normalizer (D.U : Set G), c * D.t * c⁻¹ = x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (D.oneClass D.t x D.t_order hx)
  set φ : G →* G := (MulAut.conj c).toMonoidHom with hφ
  have hφapp : ∀ g, φ g = c * g * c⁻¹ := fun g => rfl
  have hφinj : Function.Injective φ := (MulAut.conj c).injective
  set Uc := D.U.map φ
  set Sc := (D.S : Subgroup G).map φ
  -- `U ≤ U^c ⊔ S^c`.
  have hle : D.U ≤ Uc ⊔ Sc := by
    intro u hu
    have hux : x * u = u * x := (mem_centralizer_iff.mp (hcent hu)) x hxS
    have hH : c⁻¹ * u * c ∈ D.H := by
      rw [show D.H = centralizer ({D.t} : Set G) from rfl, mem_centralizer_singleton_iff]
      have ht : D.t = c⁻¹ * x * c := by rw [← hc]; group
      rw [ht]
      calc c⁻¹ * u * c * (c⁻¹ * x * c) = c⁻¹ * (u * x) * c := by group
        _ = c⁻¹ * (x * u) * c := by rw [hux]
        _ = c⁻¹ * x * c * (c⁻¹ * u * c) := by group
    rw [← hUS] at hH
    have : u = φ (c⁻¹ * u * c) := by rw [hφapp]; group
    rw [this, ← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem φ hH
  -- `S^c` normalizes `U^c` (it centralizes it).
  have hScN : Sc ≤ normalizer (Uc : Set G) := by
    apply le_normalizer_of_le_centralizer
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have hsu : s * u = u * s := (mem_centralizer_iff.mp (hcent hu)) s hs
    change (c * s * c⁻¹) * (c * u * c⁻¹) = (c * u * c⁻¹) * (c * s * c⁻¹)
    simp only [mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc s u, hsu, mul_assoc]
  have hSc : IsPGroup 2 Sc := D.S.isPGroup'.map φ
  have hUle : D.U ≤ Uc := le_of_le_sup_of_odd hScN hSc hUodd hle
  have hcard : Nat.card Uc = Nat.card D.U := Subgroup.card_map_of_injective hφinj
  have hUeq : D.U = Uc := Subgroup.eq_of_le_of_card_ge hUle hcard.le
  refine ⟨c, ?_, hc⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : φ h ∈ Uc := Subgroup.mem_map_of_mem φ hh
    rw [← hUeq, hφapp] at this
    exact this
  · intro hh
    have hh' : c * h * c⁻¹ ∈ Uc := hUeq ▸ hh
    obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp hh'
    rw [hφapp] at hu'
    have : u = h := by
      have := congrArg (fun g => c⁻¹ * g * c) hu'
      simpa [mul_assoc] using this
    exact this ▸ hu

/-- **Remark 3.5, one-class clause.** `N_G(U)` has one class of involutions (in the form of
`BGThmBProp`'s hypothesis). -/
theorem oneClass_normalizer (D : BGData G) (hUS : D.U ⊔ (D.S : Subgroup G) = D.H)
    (hcent : D.U ≤ centralizer ((D.S : Subgroup G) : Set G)) (hUodd : Odd (Nat.card D.U)) :
    ∀ x y : G, x ∈ normalizer (D.U : Set G) → y ∈ normalizer (D.U : Set G) →
      orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ normalizer (D.U : Set G), g * x * g⁻¹ = y := by
  set N := normalizer (D.U : Set G) with hN
  have hSN : (D.S : Subgroup G) ≤ N := le_normalizer_of_le_centralizer hcent
  -- every involution of `N` is `N`-conjugate to `t`
  have key : ∀ x ∈ N, orderOf x = 2 → ∃ g ∈ N, g * D.t * g⁻¹ = x := by
    intro x hxN hx
    let P : Sylow 2 N := D.S.subtype hSN
    let x' : N := ⟨x, hxN⟩
    have hx' : orderOf x' = 2 := by rw [Subgroup.orderOf_mk]; exact hx
    have hpg : IsPGroup 2 (Subgroup.zpowers x') := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hx', pow_one]
    obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N Q P
    have hxQ : x' ∈ (Q : Subgroup N) := hQ (Subgroup.mem_zpowers x')
    have hyP : n * x' * n⁻¹ ∈ (P : Subgroup N) := by
      rw [← hn, Sylow.coe_subgroup_smul]
      exact ⟨x', hxQ, rfl⟩
    have hyS : ((n : G) * x * (n : G)⁻¹) ∈ (D.S : Subgroup G) := by
      have := hyP
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at this
      simpa using this
    have hyord : orderOf ((n : G) * x * (n : G)⁻¹) = 2 := by
      have hsemi : SemiconjBy (n : G) x ((n : G) * x * (n : G)⁻¹) := by
        simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq (n : G) hsemi).symm.trans hx
    obtain ⟨c, hcN, hc⟩ := conj_t_of_mem_S D hUS hcent hUodd hyS hyord
    refine ⟨(n : G)⁻¹ * c, N.mul_mem (N.inv_mem n.2) hcN, ?_⟩
    rw [mul_inv_rev, inv_inv, show (n : G)⁻¹ * c * D.t * (c⁻¹ * (n : G))
      = (n : G)⁻¹ * (c * D.t * c⁻¹) * (n : G) by group, hc]
    group
  intro x y hxN hyN hx hy
  obtain ⟨g1, hg1, h1⟩ := key x hxN hx
  obtain ⟨g2, hg2, h2⟩ := key y hyN hy
  refine ⟨g2 * g1⁻¹, N.mul_mem hg2 (N.inv_mem hg1), ?_⟩
  rw [← h1, ← h2]
  group

end OneClass

/-! ## 3. Index 5 is impossible for `N_G(U)`, `U` odd `≠ 1`, `G` simple -/

theorem false_of_normalizer_index_five {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (U : Subgroup G) (hUodd : Odd (Nat.card U)) (hU1 : U ≠ ⊥)
    (h5 : (normalizer (U : Set G)).index = 5) : False := by
  set N := normalizer (U : Set G) with hN
  -- `G` acts faithfully on the 5 cosets of `N`.
  let f : G →* Equiv.Perm (G ⧸ N) := MulAction.toPermHom G (G ⧸ N)
  have hker : f.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      have hNtop : N = ⊤ := by
        rw [eq_top_iff]
        intro g _
        have hg : g ∈ f.ker := h ▸ Subgroup.mem_top g
        have h1 : f g (QuotientGroup.mk 1 : G ⧸ N) = (QuotientGroup.mk 1 : G ⧸ N) := by
          rw [MonoidHom.mem_ker.mp hg]; rfl
        change g • (QuotientGroup.mk 1 : G ⧸ N) = QuotientGroup.mk 1 at h1
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one] at h1
        simpa using h1
      rw [hNtop, Subgroup.index_top] at h5
      omega
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hG120 : Nat.card G ∣ 120 := by
    have := Subgroup.card_dvd_of_injective f hinj
    rwa [Nat.card_perm, show Nat.card (G ⧸ N) = N.index from rfl, h5] at this
  -- `|N| ∣ 24` and `|U| ∣ |N|`, so `|U| = 3`.
  have hNG : Nat.card N * 5 = Nat.card G := h5 ▸ N.card_mul_index
  have hN24 : Nat.card N ∣ 24 := by
    have h : Nat.card N * 5 ∣ 24 * 5 := by rw [hNG]; exact hG120
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h
  have hUN : Nat.card U ∣ Nat.card N := Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have hU24 : Nat.card U ∣ 24 := hUN.trans hN24
  have hUne1 : Nat.card U ≠ 1 := fun h => hU1 (Subgroup.card_eq_one.mp h)
  have hU3 : Nat.card U = 3 := by
    have hle : Nat.card U ≤ 24 := Nat.le_of_dvd (by norm_num) hU24
    obtain ⟨k, hk⟩ := hUodd
    interval_cases h : Nat.card U <;> omega
  -- `U` is a Sylow 3-subgroup.
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 1) (by rw [hU3, pow_one])
  obtain ⟨Q, hUQ⟩ := hUp.exists_le_sylow
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3) (G := ↥(Q : Subgroup G))).mp Q.isPGroup'
  have hQG : 3 ^ k ∣ 120 := hk ▸ (Subgroup.card_subgroup_dvd_card (Q : Subgroup G)).trans hG120
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
    have := this.trans hQG
    norm_num at this
  have h3Q : 3 ∣ 3 ^ k := by
    have h := Subgroup.card_dvd_of_le hUQ
    rw [hU3, hk] at h; exact h
  have hk1' : k = 1 := by
    rcases Nat.lt_or_ge k 1 with h | h
    · have : k = 0 := by omega
      subst this; norm_num at h3Q
    · omega
  have hQ3 : Nat.card (Q : Subgroup G) = 3 := by rw [hk, hk1', pow_one]
  have hUQeq : U = Q := Subgroup.eq_of_le_of_card_ge hUQ (by rw [hQ3, hU3])
  have hcount : Nat.card (Sylow 3 G) = 5 := by
    rw [Sylow.card_eq_index_normalizer Q, ← h5, hN, hUQeq]; rfl
  have hmod := card_sylow_modEq_one 3 G
  rw [hcount] at hmod
  exact absurd hmod (by decide)

/-! ## 4. `KNeOneProp` from Theorem B and `CentralizerSplitProp` -/

/-- **BG Remark 3.5, design leaf G8, from Theorem B**: if `G` is simple, satisfies Hypothesis 1.1
(`D : BGData G`), the hypotheses of Theorem C (maximal inverted subgroups `K₁, K₂`, the internal
direct decomposition, `B' ≠ B` and the Frobenius clause) and `C_G(t) = U · S`, then
`K₁ ⊓ K₂ ≠ ⊥`. -/
theorem kNeOne_of_thmB (hB : BGThmBProp) (hsplit : CentralizerSplitProp) : KNeOneProp := by
  intro G _instG _instFin D K1 K2 h1 h2 hdir hBne hfrob hsimple
  by_contra hK
  have hKbot : K1 ⊓ K2 = ⊥ := by simpa using hK
  -- the Frobenius clause forces `U = B`
  have hUB : D.U = D.B := by
    by_contra hne
    have hne' : D.U ≠ D.B ⊔ (K1 ⊓ K2) := by rw [hKbot]; simpa using hne
    have hF := hfrob hne'
    rw [hKbot] at hF
    exact hF.2.2.2.2.1 rfl
  have hBne_bot : D.B ≠ ⊥ := by
    intro h
    exact hBne (by rw [h]; simp)
  have hUne : D.U ≠ ⊥ := hUB ▸ hBne_bot
  have hUpi : Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) D.U := by
    rw [show D.U = Work.GW2.oddCoreIn D.H from rfl, oddCoreIn_eq_opiCoreInG]
    exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _
  have hUodd : Odd (Nat.card ↥D.U) := (odd_card_iff_isPiSubgroup_ne_two D.U).mpr hUpi
  -- `S` centralizes `U`
  have hcent : D.U ≤ centralizer ((D.S : Subgroup G) : Set G) := by
    rw [hUB, B_eq_inf_centralizer_S D]; exact inf_le_left
  -- `H = U ⊔ S`
  have hcentr : ∀ x ∈ (D.S : Subgroup G), x * D.t = D.t * x := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (S_le_H D hx) D.t (Set.mem_singleton D.t)).symm
  have hUS : D.U ⊔ (D.S : Subgroup G) = D.H :=
    hsplit G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem) D.t_order hcentr
  set N := normalizer (D.U : Set G) with hN
  have hSN : (D.S : Subgroup G) ≤ N := le_normalizer_of_le_centralizer hcent
  have hHN : D.H ≤ N := hUS ▸ sup_le Subgroup.le_normalizer hSN
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hnorm : D.U.Normal := ⟨fun u hu g => by
      have hg : g ∈ N := htop ▸ Subgroup.mem_top g
      exact (mem_normalizer_iff.mp hg u).mp hu⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D.U with h | h
    · exact hUne h
    · -- `|G|` would be odd, but `|S| = 2n` is even
      have hGodd : Odd (Nat.card G) := by
        rw [← Subgroup.card_top (G := G), ← h]; exact hUodd
      have hcard : Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
        obtain ⟨e⟩ := D.dih
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      have hdvd : 2 ∣ Nat.card G :=
        (Dvd.intro _ hcard.symm).trans (Subgroup.card_subgroup_dvd_card _)
      exact (Nat.not_even_iff_odd.mpr hGodd) (even_iff_two_dvd.mpr hdvd)
  have h5 : N.index = 5 := hB G D N hNtop hHN (oneClass_normalizer D hUS hcent hUodd)
  exact false_of_normalizer_index_five hsimple D.U hUodd hUne h5

/-- **G8 / Remark 3.5**, `Work.BG.kNeOne` in the form prescribed by design pass 26: the
conclusion `K₁ ⊓ K₂ ≠ ⊥` is derived from BG **Theorem B** and the centralizer splitting
`C_G(t) = U · S`.  (The unconditional form `Work.GW2.C16.KNeOneProp` is not available in this
workspace: by design pass 26 it is equivalent in the architecture to Theorem B, which itself
depends on the leaf `l34Exc_sfixed_ne_four`.  The formalization below adds exactly those two
hypotheses and nothing else.) -/
theorem kNeOne (hB : BGThmBProp) (hsplit : CentralizerSplitProp) :
    Work.GW2.C16.KNeOneProp :=
  kNeOne_of_thmB hB hsplit

end Work.BG
