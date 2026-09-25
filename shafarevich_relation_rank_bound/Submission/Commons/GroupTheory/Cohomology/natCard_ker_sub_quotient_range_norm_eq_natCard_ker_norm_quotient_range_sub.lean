import Mathlib
import Submission.Commons.GroupTheory.Cohomology.herbrand_finite_cyclic

open scoped BigOperators

namespace Commons.GroupTheory.Cohomology

/-- finite endomorphism version of Herbrand's lemma -/
lemma natCard_ker_quot_range_eq {Q : Type*} [CommGroup Q] [Finite Q]
    (f g : Q →* Q) (hf : g.range ≤ f.ker) (hg : f.range ≤ g.ker) :
    Nat.card (f.ker ⧸ (g.range.subgroupOf f.ker)) =
      Nat.card (g.ker ⧸ (f.range.subgroupOf g.ker)) := by
  have hcard_gr : Nat.card ↥(g.range.subgroupOf f.ker) = Nat.card ↥g.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hf).toEquiv
  have hcard_fr : Nat.card ↥(f.range.subgroupOf g.ker) = Nat.card ↥f.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hg).toEquiv
  have hQ_f : Nat.card Q = Nat.card ↥f.ker * Nat.card ↥f.range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h
    rw [h, Nat.mul_comm]
  have hQ_g : Nat.card Q = Nat.card ↥g.ker * Nat.card ↥g.range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at h
    rw [h, Nat.mul_comm]
  have hI1 : Nat.card ↥f.ker =
      Nat.card (f.ker ⧸ (g.range.subgroupOf f.ker)) * Nat.card ↥g.range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (g.range.subgroupOf f.ker)
    rw [hcard_gr] at h
    exact h
  have hI2 : Nat.card ↥g.ker =
      Nat.card (g.ker ⧸ (f.range.subgroupOf g.ker)) * Nat.card ↥f.range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.range.subgroupOf g.ker)
    rw [hcard_fr] at h
    exact h
  have hpos : 0 < Nat.card ↥f.range * Nat.card ↥g.range :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have hL : Nat.card (f.ker ⧸ (g.range.subgroupOf f.ker)) * (Nat.card ↥f.range * Nat.card ↥g.range) = Nat.card Q := by
    rw [Nat.mul_comm (Nat.card ↥f.range) (Nat.card ↥g.range), ← Nat.mul_assoc, ← hI1, ← hQ_f]
  have hR : Nat.card (g.ker ⧸ (f.range.subgroupOf g.ker)) * (Nat.card ↥f.range * Nat.card ↥g.range) = Nat.card Q := by
    rw [← Nat.mul_assoc, ← hI2, ← hQ_g]
  have key := hL.trans hR.symm
  exact Nat.mul_right_cancel hpos key

theorem natCard_ker_sub_quotient_range_norm_eq_natCard_ker_norm_quotient_range_sub
    {G U : Type*} [Group G] [CommGroup U] [MulDistribMulAction G U] [Fintype G]
    (σ : G) (hσ : Subgroup.zpowers σ = ⊤) (d Nm : U →* U)
    (hd : ∀ u : U, d u = σ • u * u⁻¹)
    (hN : ∀ u : U, Nm u = ∏ g : G, g • u)
    (W : Subgroup U) (hWstable : ∀ (g : G) (w : U), w ∈ W → g • w ∈ W)
    (hW0 : ∀ w : U, w ∈ W → (∀ g : G, g • w = w) → ∃ v ∈ W, Nm v = w)
    (hW1 : ∀ w : U, w ∈ W → Nm w = 1 → ∃ v ∈ W, w = d v)
    [Fintype (U ⧸ W)] :
    Nat.card (d.ker ⧸ (Nm.range.subgroupOf d.ker)) =
      Nat.card (Nm.ker ⧸ (d.range.subgroupOf Nm.ker)) := by
  -- sigma-fixed implies G-fixed
  have hfix : ∀ w : U, σ • w = w → ∀ g : G, g • w = w := by
    intro w hw g
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer G w := by
      rw [Subgroup.zpowers_le]; exact hw
    exact hle (by rw [hσ]; trivial)
  -- Nm is invariant under sigma
  have hNm_sigma : ∀ u : U, Nm (σ • u) = Nm u := by
    intro u
    rw [hN (σ • u), hN u]
    refine Fintype.prod_equiv (Equiv.mulRight σ) (fun g => g • (σ • u)) (fun g => g • u) ?_
    intro g; simp [mul_smul]
  -- Nm u is fixed by sigma
  have hNm_fix : ∀ u : U, σ • Nm u = Nm u := by
    intro u
    rw [hN u]
    exact herbrand_smul_prod_univ σ u
  -- d (Nm u) = 1
  have hd_Nm : ∀ u : U, d (Nm u) = 1 := by
    intro u
    rw [hd (Nm u), hNm_fix u, mul_inv_cancel]
  -- Nm (d u) = 1
  have hNm_d : ∀ u : U, Nm (d u) = 1 := by
    intro u
    rw [hd u, map_mul, map_inv, hNm_sigma u, mul_inv_cancel]
  -- the quotient
  let Q := U ⧸ W
  let π : U →* Q := QuotientGroup.mk' W
  have hmemW : ∀ x : U, x ∈ W ↔ π x = 1 := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' W]
  have hπ_one : ∀ {x : U}, x ∈ W → π x = 1 := fun hx => (hmemW _).mp hx
  have hπ_mem : ∀ {x : U}, π x = 1 → x ∈ W := fun hx => (hmemW _).mpr hx
  have hdW : W ≤ W.comap d := fun w hw => by
    rw [Subgroup.mem_comap, hd w]
    exact W.mul_mem (hWstable σ w hw) (W.inv_mem hw)
  have hNmW : W ≤ W.comap Nm := fun w hw => by
    rw [Subgroup.mem_comap, hN w]
    exact Subgroup.prod_mem W (fun g _ => hWstable g w hw)
  let dQ : Q →* Q := QuotientGroup.map W W d hdW
  let NQ : Q →* Q := QuotientGroup.map W W Nm hNmW
  have hdQ_mk : ∀ u : U, dQ (π u) = π (d u) := fun u => QuotientGroup.map_mk' W W d hdW u
  have hNQ_mk : ∀ u : U, NQ (π u) = π (Nm u) := fun u => QuotientGroup.map_mk' W W Nm hNmW u
  -- range inclusions in Q
  have hNQrange_le : NQ.range ≤ dQ.ker := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective W q
    rw [MonoidHom.mem_ker, hNQ_mk u, hdQ_mk (Nm u), hd_Nm u, map_one]
  have hdQrange_le : dQ.range ≤ NQ.ker := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective W q
    rw [MonoidHom.mem_ker, hdQ_mk u, hNQ_mk (d u), hNm_d u, map_one]
  -- LHS map
  let φd : d.ker →* dQ.ker :=
    (π.comp d.ker.subtype).codRestrict dQ.ker (fun x =>
      MonoidHom.mem_ker.mpr (by change dQ (π x.1) = 1; rw [hdQ_mk, x.2, map_one]))
  have hφd : ∀ x : d.ker, (φd x : Q) = π x.1 := fun x => rfl
  let ψ : d.ker →* (dQ.ker ⧸ (NQ.range.subgroupOf dQ.ker)) :=
    (QuotientGroup.mk' (NQ.range.subgroupOf dQ.ker)).comp φd
  have hψ_apply : ∀ x : d.ker,
      ψ x = (QuotientGroup.mk (φd x) : dQ.ker ⧸ (NQ.range.subgroupOf dQ.ker)) :=
    fun x => rfl
  have hψ_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (NQ.range.subgroupOf dQ.ker) y
    obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk'_surjective W y'.1
    have hhW : d u₀ ∈ W := hπ_mem (by rw [← hdQ_mk u₀, hu₀]; exact y'.2)
    have hhNm : Nm (d u₀) = 1 := hNm_d u₀
    obtain ⟨v, hvW, hvd⟩ := hW1 (d u₀) hhW hhNm
    have hdu : d (u₀ * v⁻¹) = 1 := by rw [map_mul, map_inv, ← hvd, mul_inv_cancel]
    refine ⟨⟨u₀ * v⁻¹, hdu⟩, ?_⟩
    have hφ : φd ⟨u₀ * v⁻¹, hdu⟩ = y' := by
      refine Subtype.ext ?_
      show π (u₀ * v⁻¹) = y'.1
      rw [map_mul, map_inv, hπ_one hvW, inv_one, mul_one, hu₀]
    show ψ ⟨u₀ * v⁻¹, hdu⟩ = (QuotientGroup.mk y' : dQ.ker ⧸ (NQ.range.subgroupOf dQ.ker))
    rw [hψ_apply]
    exact congrArg _ hφ
  have hker_ψ : ψ.ker = Nm.range.subgroupOf d.ker := by
    ext x
    rw [MonoidHom.mem_ker, hψ_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hφd,
        MonoidHom.mem_range, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨u'', rfl⟩ := QuotientGroup.mk'_surjective W q
      have hwπ : π (x.1 * (Nm u'')⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hNQ_mk u'', hq, mul_inv_cancel]
      have hwW : x.1 * (Nm u'')⁻¹ ∈ W := hπ_mem hwπ
      have hdw : d (x.1 * (Nm u'')⁻¹) = 1 := by
        rw [map_mul, map_inv, x.2, hd_Nm u'', inv_one, mul_one]
      have hwfix : σ • (x.1 * (Nm u'')⁻¹) = x.1 * (Nm u'')⁻¹ :=
        mul_inv_eq_one.mp (by rw [← hd]; exact hdw)
      obtain ⟨v, _hvW, hv⟩ := hW0 _ hwW (hfix _ hwfix)
      exact ⟨v * u'', by rw [map_mul, hv, mul_assoc, inv_mul_cancel, mul_one]⟩
    · rintro ⟨y, hy⟩
      exact ⟨π y, by rw [hNQ_mk y, hy]⟩
  have eL : Nat.card (d.ker ⧸ (Nm.range.subgroupOf d.ker)) =
      Nat.card (dQ.ker ⧸ (NQ.range.subgroupOf dQ.ker)) := by
    rw [← hker_ψ]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj).toEquiv
  -- RHS map
  let φn : Nm.ker →* NQ.ker :=
    (π.comp Nm.ker.subtype).codRestrict NQ.ker (fun x =>
      MonoidHom.mem_ker.mpr (by change NQ (π x.1) = 1; rw [hNQ_mk, x.2, map_one]))
  have hφn : ∀ x : Nm.ker, (φn x : Q) = π x.1 := fun x => rfl
  let χ : Nm.ker →* (NQ.ker ⧸ (dQ.range.subgroupOf NQ.ker)) :=
    (QuotientGroup.mk' (dQ.range.subgroupOf NQ.ker)).comp φn
  have hχ_apply : ∀ x : Nm.ker,
      χ x = (QuotientGroup.mk (φn x) : NQ.ker ⧸ (dQ.range.subgroupOf NQ.ker)) := fun x => rfl
  have hχ_surj : Function.Surjective χ := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (dQ.range.subgroupOf NQ.ker) y
    obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk'_surjective W y'.1
    have hhW : Nm u₀ ∈ W := hπ_mem (by rw [← hNQ_mk u₀, hu₀]; exact y'.2)
    have hhfix : ∀ g : G, g • (Nm u₀) = Nm u₀ := hfix (Nm u₀) (hNm_fix u₀)
    obtain ⟨v, hvW, hv⟩ := hW0 (Nm u₀) hhW hhfix
    have hNmu : Nm (u₀ * v⁻¹) = 1 := by rw [map_mul, map_inv, hv, mul_inv_cancel]
    refine ⟨⟨u₀ * v⁻¹, hNmu⟩, ?_⟩
    have hφ : φn ⟨u₀ * v⁻¹, hNmu⟩ = y' := by
      refine Subtype.ext ?_
      show π (u₀ * v⁻¹) = y'.1
      rw [map_mul, map_inv, hπ_one hvW, inv_one, mul_one, hu₀]
    show χ ⟨u₀ * v⁻¹, hNmu⟩ = (QuotientGroup.mk y' : NQ.ker ⧸ (dQ.range.subgroupOf NQ.ker))
    rw [hχ_apply]
    exact congrArg _ hφ
  have hker_χ : χ.ker = d.range.subgroupOf Nm.ker := by
    ext x
    rw [MonoidHom.mem_ker, hχ_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hφn,
        MonoidHom.mem_range, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨u'', rfl⟩ := QuotientGroup.mk'_surjective W q
      have hwπ : π (x.1 * (d u'')⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hdQ_mk u'', hq, mul_inv_cancel]
      have hwW : x.1 * (d u'')⁻¹ ∈ W := hπ_mem hwπ
      have hNw : Nm (x.1 * (d u'')⁻¹) = 1 := by
        rw [map_mul, map_inv, x.2, hNm_d u'', inv_one, mul_one]
      obtain ⟨v, _hvW, hv⟩ := hW1 _ hwW hNw
      exact ⟨v * u'', by rw [map_mul, ← hv, mul_assoc, inv_mul_cancel, mul_one]⟩
    · rintro ⟨y, hy⟩
      exact ⟨π y, by rw [hdQ_mk y, hy]⟩
  have eR : Nat.card (Nm.ker ⧸ (d.range.subgroupOf Nm.ker)) =
      Nat.card (NQ.ker ⧸ (dQ.range.subgroupOf NQ.ker)) := by
    rw [← hker_χ]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective χ hχ_surj).toEquiv
  have eQ : Nat.card (dQ.ker ⧸ (NQ.range.subgroupOf dQ.ker)) =
      Nat.card (NQ.ker ⧸ (dQ.range.subgroupOf NQ.ker)) :=
    natCard_ker_quot_range_eq dQ NQ hNQrange_le hdQrange_le
  exact eL.trans (eQ.trans eR.symm)

end Commons.GroupTheory.Cohomology
