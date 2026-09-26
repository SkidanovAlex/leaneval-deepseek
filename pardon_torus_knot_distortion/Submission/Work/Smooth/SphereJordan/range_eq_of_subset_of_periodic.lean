import Mathlib
import Submission.Work.Smooth.SphereJordan.lift_shift_eq_pm_one

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-! ## Two parameters carrying the same value differ by a period

If a closed curve is `2π`-periodic and injective on one period `[0, 2π)`, then two parameters with
the same image differ by an integer multiple of `2π`.  This is the "period lattice" form of
injectivity, and is the only place where the injectivity hypotheses are used. -/
theorem exists_int_sub_eq_of_periodic_injOn {f : ℝ → ℂ}
    (hfp : Function.Periodic f (2 * Real.pi)) (hfi : Set.InjOn f (Set.Ico 0 (2 * Real.pi)))
    {x y : ℝ} (h : f x = f y) : ∃ k : ℤ, x - y = (k : ℝ) * (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  letI : Fact (0 < 2 * Real.pi) := ⟨hπ⟩
  let x' : ℝ := ((AddCircle.equivIco (2 * Real.pi) 0 (x : AddCircle (2 * Real.pi))) : ℝ)
  let y' : ℝ := ((AddCircle.equivIco (2 * Real.pi) 0 (y : AddCircle (2 * Real.pi))) : ℝ)
  have hx'mem : x' ∈ Set.Ico 0 (2 * Real.pi) := by
    change ((AddCircle.equivIco (2 * Real.pi) 0 (x : AddCircle (2 * Real.pi))) : ℝ)
      ∈ Set.Ico 0 (2 * Real.pi)
    simpa using (AddCircle.equivIco (2 * Real.pi) 0 (x : AddCircle (2 * Real.pi))).coe_prop
  have hy'mem : y' ∈ Set.Ico 0 (2 * Real.pi) := by
    change ((AddCircle.equivIco (2 * Real.pi) 0 (y : AddCircle (2 * Real.pi))) : ℝ)
      ∈ Set.Ico 0 (2 * Real.pi)
    simpa using (AddCircle.equivIco (2 * Real.pi) 0 (y : AddCircle (2 * Real.pi))).coe_prop
  have hx'coe : (x' : AddCircle (2 * Real.pi)) = x := AddCircle.coe_equivIco
  have hy'coe : (y' : AddCircle (2 * Real.pi)) = y := AddCircle.coe_equivIco
  obtain ⟨kx, hkx⟩ : ∃ k : ℤ, x' - x = (k : ℝ) * (2 * Real.pi) := by
    have hmem : x' - x ∈ AddSubgroup.zmultiples (2 * Real.pi) :=
      QuotientAddGroup.eq_iff_sub_mem.mp hx'coe
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    exact ⟨k, by rw [← hk, zsmul_eq_mul]⟩
  obtain ⟨ky, hky⟩ : ∃ k : ℤ, y' - y = (k : ℝ) * (2 * Real.pi) := by
    have hmem : y' - y ∈ AddSubgroup.zmultiples (2 * Real.pi) :=
      QuotientAddGroup.eq_iff_sub_mem.mp hy'coe
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    exact ⟨k, by rw [← hk, zsmul_eq_mul]⟩
  have hxval : f x = f x' := by
    have hxe : x = x' + (-(kx : ℝ)) * (2 * Real.pi) := by linarith
    rw [hxe]
    simpa using hfp.int_mul (-kx) x'
  have hyval : f y = f y' := by
    have hye : y = y' + (-(ky : ℝ)) * (2 * Real.pi) := by linarith
    rw [hye]
    simpa using hfp.int_mul (-ky) y'
  have hxy' : x' = y' := hfi hx'mem hy'mem (by rw [← hxval, h, hyval])
  refine ⟨ky - kx, ?_⟩
  have hcast : ((ky - kx : ℤ) : ℝ) = (ky : ℝ) - (kx : ℝ) := by push_cast; ring
  rw [hcast]
  linarith

/-- Iterating the shift of a lift by one period. -/
theorem shift_int_two_pi (Ψ : ℝ → ℝ) (d : ℤ)
    (h : ∀ θ : ℝ, Ψ (θ + 2 * Real.pi) = Ψ θ + (d : ℝ) * (2 * Real.pi)) :
    ∀ (θ : ℝ) (k : ℤ),
      Ψ (θ + (k : ℝ) * (2 * Real.pi)) = Ψ θ + (k : ℝ) * (d : ℝ) * (2 * Real.pi) := by
  have hnat : ∀ (θ : ℝ) (n : ℕ),
      Ψ (θ + (n : ℝ) * (2 * Real.pi)) = Ψ θ + (n : ℝ) * (d : ℝ) * (2 * Real.pi) := by
    intro θ n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : θ + ((n : ℕ) + 1 : ℕ) * (2 * Real.pi)
          = (θ + (n : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
      rw [h1, h, ih]; push_cast; ring
  have hneg : ∀ (θ : ℝ) (n : ℕ),
      Ψ (θ - (n : ℝ) * (2 * Real.pi)) = Ψ θ - (n : ℝ) * (d : ℝ) * (2 * Real.pi) := by
    intro θ n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : θ - ((n : ℕ) + 1 : ℕ) * (2 * Real.pi)
          = (θ - (n : ℝ) * (2 * Real.pi)) - 2 * Real.pi := by push_cast; ring
      have h2 : Ψ ((θ - (n : ℝ) * (2 * Real.pi)) - 2 * Real.pi)
          = Ψ (θ - (n : ℝ) * (2 * Real.pi)) - (d : ℝ) * (2 * Real.pi) := by
        have h3 := h ((θ - (n : ℝ) * (2 * Real.pi)) - 2 * Real.pi)
        have h4 : (θ - (n : ℝ) * (2 * Real.pi) - 2 * Real.pi) + 2 * Real.pi
            = θ - (n : ℝ) * (2 * Real.pi) := by ring
        rw [h4] at h3
        linarith
      rw [h1, h2, ih]; push_cast; ring
  intro θ k
  rcases k with n | n
  · simpa using hnat θ n
  · have hk : ((Int.negSucc n : ℤ) : ℝ) = -((n : ℝ) + 1) := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [hk]
    have h1 : θ + (-((n : ℝ) + 1)) * (2 * Real.pi)
        = θ - ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [h1, hneg θ (n + 1)]
    push_cast; ring

/-! ## A continuous lift of one periodic curve through another

If `f, g : ℝ → ℂ` are continuous `2π`-periodic and `g` is injective on one period, then the image of
`g` is a (topological) circle, and `g` is a covering map onto its image.  Hence any map into the
image of `g` — in particular `f` when `range f ⊆ range g` — admits a continuous lift to `ℝ`. -/
theorem exists_continuous_lift_periodic {f g : ℝ → ℂ} (hf : Continuous f)
    (hfp : Function.Periodic f (2 * Real.pi)) (hfi : Set.InjOn f (Set.Ico 0 (2 * Real.pi)))
    (hg : Continuous g) (hgp : Function.Periodic g (2 * Real.pi))
    (hgi : Set.InjOn g (Set.Ico 0 (2 * Real.pi))) (hsub : Set.range f ⊆ Set.range g) :
    ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧ ∀ x, g (Ψ x) = f x := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  letI : Fact (0 < 2 * Real.pi) := ⟨hπ⟩
  -- The map induced by `g` on the circle `ℝ/2πℤ`.
  let Φ : AddCircle (2 * Real.pi) → ℂ := AddCircle.liftIco (2 * Real.pi) 0 g
  have hΦcont : Continuous Φ :=
    AddCircle.liftIco_zero_continuous (by simpa using (hgp 0).symm) hg.continuousOn
  have hΦcoe : ∀ t : ℝ, Φ (t : AddCircle (2 * Real.pi)) = g t := by
    intro t
    let x : ℝ := ((AddCircle.equivIco (2 * Real.pi) 0 (t : AddCircle (2 * Real.pi))) : ℝ)
    have hxmem : x ∈ Set.Ico 0 (2 * Real.pi) := by
      change ((AddCircle.equivIco (2 * Real.pi) 0 (t : AddCircle (2 * Real.pi))) : ℝ)
        ∈ Set.Ico 0 (2 * Real.pi)
      simpa using (AddCircle.equivIco (2 * Real.pi) 0 (t : AddCircle (2 * Real.pi))).coe_prop
    have hxcoe : (x : AddCircle (2 * Real.pi)) = t := AddCircle.coe_equivIco
    have h1 : Φ (x : AddCircle (2 * Real.pi)) = g x :=
      AddCircle.liftIco_coe_apply (by simpa using hxmem)
    have hgxt : g x = g t := by
      have hmem : x - t ∈ AddSubgroup.zmultiples (2 * Real.pi) :=
        QuotientAddGroup.eq_iff_sub_mem.mp hxcoe
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
      have hk' : (k : ℝ) * (2 * Real.pi) = x - t := by rw [← hk, zsmul_eq_mul]
      have ht : t = x + (-(k : ℝ)) * (2 * Real.pi) := by linarith
      rw [ht]
      simpa using (hgp.int_mul (-k) x).symm
    rw [hxcoe] at h1
    rw [h1, hgxt]
  have hrangeΦ : Set.range Φ = Set.range g := by
    apply Set.Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      obtain ⟨t, _, rfl⟩ := AddCircle.eq_coe_Ico q
      exact ⟨t, (hΦcoe t).symm⟩
    · rintro _ ⟨t, rfl⟩
      exact ⟨(t : AddCircle (2 * Real.pi)), hΦcoe t⟩
  have hΦinj : Function.Injective Φ := by
    intro q q' hqq
    obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ico q
    obtain ⟨y, hy, rfl⟩ := AddCircle.eq_coe_Ico q'
    have hgy : g x = g y := by rw [← hΦcoe x, ← hΦcoe y, hqq]
    rw [hgi hx hy hgy]
  -- The induced map, landed in the image of `g`.
  let Φ' : AddCircle (2 * Real.pi) → Set.range g :=
    fun q => ⟨Φ q, by rw [← hrangeΦ]; exact Set.mem_range_self q⟩
  have hΦ'cont : Continuous Φ' := Continuous.subtype_mk hΦcont _
  have hΦ'coe : ∀ q : AddCircle (2 * Real.pi), (Φ' q).1 = Φ q := fun q => rfl
  have hΦ'inj : Function.Injective Φ' := by
    intro q q' h
    exact hΦinj (congrArg Subtype.val h)
  have hΦ'emb : Topology.IsEmbedding Φ' := (hΦ'cont.isClosedEmbedding hΦ'inj).toIsEmbedding
  let Φ'h : AddCircle (2 * Real.pi) ≃ₜ Set.range Φ' := hΦ'emb.toHomeomorph
  -- `f` lands in the image of the embedding, hence is a self-map of the circle after transfer.
  have hf'mem : ∀ x : ℝ,
      (⟨f x, hsub (Set.mem_range_self x)⟩ : Set.range g) ∈ Set.range Φ' := by
    intro x
    obtain ⟨t, ht⟩ := hsub (Set.mem_range_self x)
    exact ⟨(t : AddCircle (2 * Real.pi)), Subtype.ext (by rw [hΦ'coe, hΦcoe t, ht])⟩
  let f' : ℝ → Set.range Φ' :=
    fun x => ⟨⟨f x, hsub (Set.mem_range_self x)⟩, hf'mem x⟩
  have hf'cont : Continuous f' :=
    Continuous.subtype_mk (Continuous.subtype_mk hf (fun x => hsub (Set.mem_range_self x))) hf'mem
  let τ : C(ℝ, AddCircle (2 * Real.pi)) :=
    ⟨fun x => Φ'h.symm (f' x), Φ'h.symm.continuous.comp hf'cont⟩
  -- Lift `τ` through the covering map `ℝ → ℝ/2πℤ` (`ℝ` is simply connected).
  let e₀ : ℝ := ((AddCircle.equivIco (2 * Real.pi) 0 (τ 0)) : ℝ)
  have he : ((↑) : ℝ → AddCircle (2 * Real.pi)) e₀ = τ 0 := AddCircle.coe_equivIco
  obtain ⟨Ψ, ⟨-, hΨlift⟩, -⟩ := IsCoveringMap.existsUnique_continuousMap_lifts
    (AddCircle.isCoveringMap_coe (2 * Real.pi)) τ 0 e₀ he
  refine ⟨Ψ, Ψ.continuous, fun x => ?_⟩
  have hτx : τ x = ((Ψ x : ℝ) : AddCircle (2 * Real.pi)) := (congr_fun hΨlift x).symm
  have hkey : Φ' (τ x) = (⟨f x, hsub (Set.mem_range_self x)⟩ : Set.range g) := by
    have h2 := Topology.IsEmbedding.toHomeomorph_apply_coe hΦ'emb (Φ'h.symm (f' x))
    rw [Homeomorph.apply_symm_apply] at h2
    exact h2.symm
  rw [hτx] at hkey
  have hval : (Φ' ((Ψ x : ℝ) : AddCircle (2 * Real.pi))).1 = g (Ψ x) := by
    rw [hΦ'coe]; exact hΦcoe (Ψ x)
  have h1 := congrArg (fun y : Set.range g => (y : ℂ)) hkey
  rw [hval] at h1
  exact h1

/-- **A simple closed curve contained in another is equal to it.**

Let `f, g : ℝ → ℂ` be continuous `2π`-periodic curves which are injective on `[0, 2π)`.  If the image
of `f` is contained in the image of `g`, then the two images are equal.

Indeed, `g` presents its image as a circle, so `f` admits a continuous lift `Ψ` along `g`
(`exists_continuous_lift_periodic`).  The shift of `Ψ` over one period is an integer multiple `d·2π`
(a continuous `(2πℤ)`-valued function on `ℝ` is constant), and `lift_shift_eq_pm_one` gives
`d = ±1`.  Then `Ψ` is surjective: its image contains an interval of length `2π`, and the shifts
translate this interval by multiples of `2π`.  Hence every parameter of `g` is a parameter of `f`,
i.e. `range g ⊆ range f`. -/
theorem range_eq_of_subset_of_periodic {f g : ℝ → ℂ} (hf : Continuous f)
    (hfp : ∀ x : ℝ, f (x + 2 * Real.pi) = f x) (hfi : Set.InjOn f (Set.Ico 0 (2 * Real.pi)))
    (hg : Continuous g) (hgp : ∀ x : ℝ, g (x + 2 * Real.pi) = g x)
    (hgi : Set.InjOn g (Set.Ico 0 (2 * Real.pi))) (hsub : Set.range f ⊆ Set.range g) :
    Set.range f = Set.range g := by
  have hfpP : Function.Periodic f (2 * Real.pi) := hfp
  have hgpP : Function.Periodic g (2 * Real.pi) := hgp
  obtain ⟨Ψ, hΨcont, hgΨ⟩ :=
    exists_continuous_lift_periodic hf hfpP hfi hg hgpP hgi hsub
  -- The shift over one period lies in the period lattice.
  have hmem : ∀ x : ℝ, Ψ (x + 2 * Real.pi) - Ψ x ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
    intro x
    have hg_eq : g (Ψ (x + 2 * Real.pi)) = g (Ψ x) := by
      rw [hgΨ, hgΨ]
      exact hfp x
    obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hgpP hgi hg_eq
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by rw [zsmul_eq_mul]; exact hk.symm⟩
  -- It is a continuous function into a discrete set, hence constant.
  let Δ : ℝ := Ψ (2 * Real.pi) - Ψ 0
  have hδconst : ∀ x : ℝ, Ψ (x + 2 * Real.pi) - Ψ x = Δ := by
    let δ : ℝ → AddSubgroup.zmultiples (2 * Real.pi) :=
      fun x => ⟨Ψ (x + 2 * Real.pi) - Ψ x, hmem x⟩
    have hδcont : Continuous δ :=
      Continuous.subtype_mk
        ((hΨcont.comp (continuous_id.add continuous_const)).sub hΨcont) hmem
    have hlc : IsLocallyConstant δ := (IsLocallyConstant.iff_continuous δ).mpr hδcont
    intro x
    have h2 := hlc.apply_eq_of_isPreconnected (s := Set.univ) isPreconnected_univ
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)
    have h3 : (δ 0 : ℝ) = (δ x : ℝ) := congrArg Subtype.val h2
    simp only [δ, zero_add] at h3
    rw [← h3]
  have hΔmem : Δ ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
    have h := hmem 0
    rw [hδconst 0] at h
    exact h
  obtain ⟨d, hd⟩ := AddSubgroup.mem_zmultiples_iff.mp hΔmem
  have hd' : (d : ℝ) * (2 * Real.pi) = Δ := by rw [← hd, zsmul_eq_mul]
  have hshift : ∀ θ : ℝ, Ψ (θ + 2 * Real.pi) = Ψ θ + (d : ℝ) * (2 * Real.pi) := by
    intro θ
    have h := hδconst θ
    linarith [h, hd']
  -- The shift of the parameter is the period lattice, by injectivity of `f`.
  have hmod : ∀ x y : ℝ, (∃ k : ℤ, Ψ x - Ψ y = (k : ℝ) * (2 * Real.pi)) →
      (∃ k : ℤ, x - y = (k : ℝ) * (2 * Real.pi)) := by
    intro x y hk
    obtain ⟨k, hk⟩ := hk
    have hΨxy : Ψ x = Ψ y + (k : ℝ) * (2 * Real.pi) := by linarith
    have hg_eq : g (Ψ x) = g (Ψ y) := by
      rw [hΨxy]
      exact hgpP.int_mul k (Ψ y)
    rw [hgΨ, hgΨ] at hg_eq
    exact exists_int_sub_eq_of_periodic_injOn hfpP hfi hg_eq
  have hdpm : d = 1 ∨ d = -1 := lift_shift_eq_pm_one Ψ hΨcont d hshift hmod
  -- Surjectivity of the lift.
  have hsurj : ∀ y : ℝ, ∃ x : ℝ, Ψ x = y := by
    intro y
    have hcpos : (0 : ℝ) < 2 * Real.pi := by positivity
    have key1 : d = 1 → ∃ x : ℝ, Ψ x = y := by
      intro h1
      set n : ℤ := ⌊(y - Ψ 0) / (2 * Real.pi)⌋ with hn
      set t : ℝ := y - (n : ℝ) * (2 * Real.pi) with ht
      have htlo : Ψ 0 ≤ t := by
        have h := Int.floor_le ((y - Ψ 0) / (2 * Real.pi))
        rw [← hn] at h
        have h2 : (n : ℝ) * (2 * Real.pi) ≤ y - Ψ 0 := by
          have h3 := mul_le_mul_of_nonneg_right h (le_of_lt hcpos)
          rwa [div_mul_cancel₀ _ (ne_of_gt hcpos)] at h3
        linarith [ht]
      have hthi : t ≤ Ψ (2 * Real.pi) := by
        have h := Int.lt_floor_add_one ((y - Ψ 0) / (2 * Real.pi))
        rw [← hn] at h
        have h2 : y - Ψ 0 < ((n : ℝ) + 1) * (2 * Real.pi) := by
          have h3 := mul_lt_mul_of_pos_right h hcpos
          rwa [div_mul_cancel₀ _ (ne_of_gt hcpos)] at h3
        have hshift0 : Ψ (0 + 2 * Real.pi) = Ψ 0 + (d : ℝ) * (2 * Real.pi) := hshift 0
        rw [zero_add] at hshift0
        rw [hshift0, h1, ht]
        push_cast
        linarith
      obtain ⟨u, -, huu⟩ := (intermediate_value_Icc (le_of_lt hcpos) hΨcont.continuousOn)
        (show t ∈ Set.Icc (Ψ 0) (Ψ (2 * Real.pi)) from ⟨htlo, hthi⟩)
      refine ⟨u + (n : ℝ) * (2 * Real.pi), ?_⟩
      have hiter := shift_int_two_pi Ψ d hshift u n
      rw [hiter, huu, h1]
      simp only [Int.cast_one, mul_one]
      rw [ht]; ring
    have key2 : d = -1 → ∃ x : ℝ, Ψ x = y := by
      intro h1
      set n : ℤ := ⌊(Ψ 0 - y) / (2 * Real.pi)⌋ with hn
      set t : ℝ := y + (n : ℝ) * (2 * Real.pi) with ht
      have htlo : Ψ (2 * Real.pi) ≤ t := by
        have h := Int.lt_floor_add_one ((Ψ 0 - y) / (2 * Real.pi))
        rw [← hn] at h
        have h2 : Ψ 0 - y < ((n : ℝ) + 1) * (2 * Real.pi) := by
          have h3 := mul_lt_mul_of_pos_right h hcpos
          rwa [div_mul_cancel₀ _ (ne_of_gt hcpos)] at h3
        have hshift0 : Ψ (0 + 2 * Real.pi) = Ψ 0 + (d : ℝ) * (2 * Real.pi) := hshift 0
        rw [zero_add] at hshift0
        rw [hshift0, h1, ht]
        push_cast
        linarith
      have hthi : t ≤ Ψ 0 := by
        have h := Int.floor_le ((Ψ 0 - y) / (2 * Real.pi))
        rw [← hn] at h
        have h2 : (n : ℝ) * (2 * Real.pi) ≤ Ψ 0 - y := by
          have h3 := mul_le_mul_of_nonneg_right h (le_of_lt hcpos)
          rwa [div_mul_cancel₀ _ (ne_of_gt hcpos)] at h3
        linarith [ht]
      obtain ⟨u, -, huu⟩ := (intermediate_value_Icc' (le_of_lt hcpos) hΨcont.continuousOn)
        (show t ∈ Set.Icc (Ψ (2 * Real.pi)) (Ψ 0) from ⟨htlo, hthi⟩)
      refine ⟨u + (n : ℝ) * (2 * Real.pi), ?_⟩
      have hiter := shift_int_two_pi Ψ d hshift u n
      rw [hiter, huu, h1]
      simp only [Int.cast_neg, Int.cast_one]
      rw [ht]; ring
    rcases hdpm with h1 | h1
    · exact key1 h1
    · exact key2 h1
  apply Set.Subset.antisymm hsub
  rintro _ ⟨a, rfl⟩
  obtain ⟨x, hx⟩ := hsurj a
  exact ⟨x, by rw [← hgΨ x, hx]⟩

end

end Work.Smooth.SphereJordan
