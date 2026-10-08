import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

theorem step11Out_free_lines {G : Type} [Group G] [Finite G]
    {R P T D : Subgroup G} {s : G}
    (hcomm : IsMulCommutative ↥R) (hPR : P ≤ R)
    (hTchar : ∀ a ∈ R, a ∈ T ↔ s * a * s⁻¹ = a⁻¹)
    (hDCP : D ≤ Subgroup.centralizer (P : Set G))
    (hs2 : s * s = 1) (hs_ne : s ≠ 1) (hsD : s ∈ D) (hsR : s ∈ Subgroup.normalizer (R : Set G))
    (hp : (Nat.card P).Prime) (hexp : ∀ x ∈ R, x ^ Nat.card P = 1)
    (hfpf : ∀ x ∈ R, x ∉ P → ∀ y ∈ D, y * x * y⁻¹ * x⁻¹ ∈ P → y = 1)
    (hsC : ∀ y ∈ D, y * s * y⁻¹ = s) :
    ∀ y ∈ D, ∀ A : Subgroup G, A ≤ R → Nat.card A = Nat.card P → A ≠ P → ¬ A ≤ T →
      A.map (MulAut.conj y).toMonoidHom = A → y = 1 := by
  intro y hyD A hAR hAcard hAne hAnT hyA
  -- elements of `R` commute with one another, as elements of `G`
  have commR : ∀ {u v : G}, u ∈ R → v ∈ R → u * v = v * u := by
    intro u v hu hv
    have h := (hcomm.is_comm).comm (⟨u, hu⟩ : ↥R) (⟨v, hv⟩ : ↥R)
    simpa using congrArg Subtype.val h
  -- **Step A.** An element of `R` fixed by conjugation by `s` lies in `P`.
  have stepA : ∀ x ∈ R, s * x * s⁻¹ = x → x ∈ P := by
    intro x hxR hfix
    by_contra hxP
    have hmem : s * x * s⁻¹ * x⁻¹ ∈ P := by rw [hfix]; simp
    exact hs_ne (hfpf x hxR hxP s hsD hmem)
  -- pick `a ∈ A \ T`
  have hAnT' : ∃ a, a ∈ A ∧ a ∉ T := by
    by_contra h
    apply hAnT
    intro x hx
    by_contra hxT
    exact h ⟨x, hx, hxT⟩
  obtain ⟨a, haA, haT⟩ := hAnT'
  have haR : a ∈ R := hAR haA
  have h1T : (1 : G) ∈ T := (hTchar 1 R.one_mem).mpr (by simp)
  have ha_ne1 : a ≠ 1 := by
    intro h; apply haT; rw [h]; exact h1T
  -- `orderOf a = p`
  have hap : a ^ Nat.card P = 1 := hexp a haR
  have horda : orderOf a = Nat.card P := by
    rcases hp.eq_one_or_self_of_dvd (orderOf a) (orderOf_dvd_iff_pow_eq_one.mpr hap) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ha_ne1
    · exact h1
  -- `A = ⟨a⟩`
  have hAeq : A = Subgroup.zpowers a := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA) (le_of_eq ?_)
    rw [Nat.card_zpowers, horda, hAcard]
  -- `a ∉ P` (else `A = P`)
  have haP : a ∉ P := by
    intro ha_mem
    have hPz : P = Subgroup.zpowers a := by
      symm
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha_mem) (le_of_eq ?_)
      rw [Nat.card_zpowers, horda]
    have hPleA : P ≤ A := by rw [hPz]; exact Subgroup.zpowers_le.mpr haA
    exact hAne ((Subgroup.eq_of_le_of_card_ge hPleA (le_of_eq hAcard)).symm)
  -- `y a y⁻¹ ∈ A = ⟨a⟩`, giving `k` with `a ^ k = y a y⁻¹`
  have hya_mem : y * a * y⁻¹ ∈ A := by
    have h1 : (MulAut.conj y) a ∈ A.map (MulAut.conj y).toMonoidHom :=
      Subgroup.mem_map_of_mem _ haA
    rw [hyA] at h1
    rwa [MulAut.conj_apply] at h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← hAeq]; exact hya_mem)
  -- `b = s a s⁻¹`
  set b : G := s * a * s⁻¹ with hbdef
  have hbR : b ∈ R := by
    rw [hbdef]
    exact (Subgroup.mem_normalizer_iff.mp hsR a).mp haR
  have hs_inv2 : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev s s, hs2, inv_one]
  have hsbs : s * b * s⁻¹ = a := by
    rw [hbdef]
    calc s * (s * a * s⁻¹) * s⁻¹ = (s * s) * a * (s⁻¹ * s⁻¹) := by group
      _ = a := by rw [hs2, hs_inv2]; group
  -- `e = a * b ∈ P \ {1}`
  set e : G := a * b with hedef
  have heR : e ∈ R := by rw [hedef]; exact R.mul_mem haR hbR
  have hphi_e : s * e * s⁻¹ = e := by
    rw [hedef]
    have h1 : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
    rw [h1, show s * a * s⁻¹ = b from hbdef.symm, hsbs]
    exact commR hbR haR
  have heP : e ∈ P := stepA e heR hphi_e
  have he_ne1 : e ≠ 1 := by
    intro he
    apply haT
    rw [hTchar a haR]
    have hab : a * b = 1 := by rw [← hedef]; exact he
    have hb_eq : b = a⁻¹ := (mul_eq_one_iff_inv_eq.mp hab).symm
    rw [hbdef] at hb_eq
    exact hb_eq
  -- `y` commutes with `s`
  have hy_s : y * s * y⁻¹ = s := hsC y hyD
  have hy_comm_s : y * s = s * y := by
    calc y * s = (y * s * y⁻¹) * y := by group
      _ = s * y := by rw [hy_s]
  have hy_comm_si : s⁻¹ * y⁻¹ = y⁻¹ * s⁻¹ := by
    rw [← mul_inv_rev y s, hy_comm_s, mul_inv_rev]
  -- `y b y⁻¹ = b ^ k`
  have hyb : y * b * y⁻¹ = b ^ k := by
    rw [hbdef]
    have h1 : y * (s * a * s⁻¹) * y⁻¹ = s * (y * a * y⁻¹) * s⁻¹ := by
      calc y * (s * a * s⁻¹) * y⁻¹ = (y * s) * a * (s⁻¹ * y⁻¹) := by group
        _ = (s * y) * a * (y⁻¹ * s⁻¹) := by rw [hy_comm_s, hy_comm_si]
        _ = s * (y * a * y⁻¹) * s⁻¹ := by group
    rw [h1, ← hk]
    have hmz := map_zpow (MulAut.conj s).toMonoidHom a k
    simpa [MulAut.conj_apply] using hmz
  -- `y e y⁻¹ = e ^ k`
  have hye : y * e * y⁻¹ = e ^ k := by
    rw [hedef]
    have h1 : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [h1, ← hk, hyb]
    exact (Commute.mul_zpow (commR haR hbR) k).symm
  -- but `y` centralises `e ∈ P`, so `e ^ k = e`
  have hec : y * e * y⁻¹ = e := by
    have hcy : e * y = y * e := (Subgroup.mem_centralizer_iff.mp (hDCP hyD)) e heP
    rw [← hcy]; group
  have hek : e ^ k = e := by rw [← hye]; exact hec
  have horde : orderOf e = Nat.card P := by
    rcases hp.eq_one_or_self_of_dvd (orderOf e)
      (orderOf_dvd_iff_pow_eq_one.mpr (hexp e (hPR heP))) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) he_ne1
    · exact h1
  have hekm1 : e ^ (k - 1) = 1 := by rw [zpow_sub_one, hek]; group
  have hkm1 : ((Nat.card P : ℤ)) ∣ (k - 1) := by
    have h := (orderOf_dvd_iff_zpow_eq_one (x := e) (i := k - 1)).mpr hekm1
    rwa [horde] at h
  -- hence `a ^ k = a`, i.e. `y` centralises `a`
  have hak : a ^ k = a := by
    obtain ⟨m, hm⟩ := hkm1
    have hk_eq : k = ((Nat.card P : ℤ)) * m + 1 := by omega
    rw [hk_eq, zpow_add, zpow_mul, zpow_natCast, hap, one_zpow, one_mul, zpow_one]
  have hya_eq : y * a * y⁻¹ = a := by rw [← hk, hak]
  -- so `[y, a] = 1 ∈ P`, and `a ∈ R \ P`, whence `y = 1`
  have haymem : y * a * y⁻¹ * a⁻¹ ∈ P := by
    have : y * a * y⁻¹ * a⁻¹ = 1 := by rw [hya_eq]; group
    rw [this]; exact P.one_mem
  exact hfpf a haR haP y hyD haymem

end Work.ThmF.ChV3.Prove
