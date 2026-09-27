import Mathlib
import Submission.Work.Mostow.nearIdAt_conj
import Submission.Work.Mostow.finite_shortAt
import Submission.Work.Mostow.volH_le_card_mul_of_ae_count

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-!
# `Work.Mostow.ftbUnfold`

Unfolding the near-identity locus at a stratum, in general dimension.

Everything here is the general-`n` transcription of the `n = 3` argument of
`Submission/Work/Mostow/gapA/unfoldTube.lean`, with the `Cℓ`-bounding hypothesis on the number of
conjugates of `b` that are `η₁`-near-identity at a common point playing the role of `hconj`
(which for `n = 3` forces that number to be at most `2`).
-/

/-! ## 1. Measurability of the near-identity locus

The set `{u | NearIdAt b u η} = {u | ∀ v, hdist u v ≤ 1 → hdist v (b • v) < η}` is Borel: it is
the union over `k` of the closed sets of points at distance `≥ 1 + 1/(k+1)` from the complement of
the open set `S = {v | hdist v (b • v) < η}`. -/

theorem ftbMeasurableSetNearId (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (b : PO n 1) (η : ℝ) : MeasurableSet {u : E n | NearIdAt b u η} := by
  have hdist_cont : Continuous (fun p : E n × E n => hdist p.1 p.2) := hI.2.2.2.2.1
  have hsmul_b : Continuous (fun u : E n => b • u) := (hI.2.2.2.2.2.2.2.2.1 b).continuous
  have hcompact : ∀ (u : E n) (r : ℝ), IsCompact {v : E n | hdist u v ≤ r} := hI.2.2.2.2.2.1
  set S : Set (E n) := {u : E n | hdist u (b • u) < η} with hS
  have hScont : Continuous fun u : E n => hdist u (b • u) := by
    change Continuous ((fun p : E n × E n => hdist p.1 p.2) ∘ (fun u : E n => (u, b • u)))
    exact hdist_cont.comp (Continuous.prodMk continuous_id hsmul_b)
  have hSopen : IsOpen S := hScont.isOpen_preimage _ isOpen_Iio
  have hSclosed : IsClosed Sᶜ := hSopen.isClosed_compl
  have hAcl : ∀ k : ℕ,
      IsClosed {w : E n | ∀ u : ↥Sᶜ, (1 + 1 / ((k : ℝ) + 1)) ≤ hdist w (u : E n)} := by
    intro k
    have heq : {w : E n | ∀ u : ↥Sᶜ, (1 + 1 / ((k : ℝ) + 1)) ≤ hdist w (u : E n)}
        = ⋂ u : ↥Sᶜ, {w : E n | (1 + 1 / ((k : ℝ) + 1)) ≤ hdist w (u : E n)} := by
      ext w; simp
    rw [heq]
    refine isClosed_iInter fun u => ?_
    have hcont_u : Continuous (fun w : E n => hdist w (u : E n)) := by
      change Continuous ((fun p : E n × E n => hdist p.1 p.2) ∘ (fun w : E n => (w, (u : E n))))
      exact hdist_cont.comp (Continuous.prodMk continuous_id continuous_const)
    exact isClosed_le continuous_const hcont_u
  have hsub : {u : E n | NearIdAt b u η} ⊆
      ⋃ k : ℕ, {w : E n | ∀ u : ↥Sᶜ, (1 + 1 / ((k : ℝ) + 1)) ≤ hdist w (u : E n)} := by
    intro w hw
    rw [Set.mem_iUnion]
    by_cases hne : (Sᶜ : Set (E n)).Nonempty
    · obtain ⟨u₀, hu₀⟩ := hne
      have hKc : IsCompact ({v : E n | hdist w v ≤ hdist w u₀ + 1} ∩ Sᶜ) :=
        (hcompact w (hdist w u₀ + 1)).inter_right hSclosed
      have hKne : ({v : E n | hdist w v ≤ hdist w u₀ + 1} ∩ Sᶜ).Nonempty :=
        ⟨u₀, by simp [hu₀]⟩
      have hcont_w : Continuous (fun v : E n => hdist w v) := by
        change Continuous ((fun p : E n × E n => hdist p.1 p.2) ∘ (fun v : E n => (w, v)))
        exact hdist_cont.comp (Continuous.prodMk continuous_const continuous_id)
      obtain ⟨u₁, hu₁, hmin⟩ := hKc.exists_isMinOn hKne hcont_w.continuousOn
      have hgt : 1 < hdist w u₁ := by
        by_contra hle
        exact hu₁.2 (hw u₁ (not_lt.mp hle))
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hgt)
      refine ⟨k, ?_⟩
      intro u
      have hcase : ∀ v : ↥Sᶜ, hdist w u₁ ≤ hdist w (v : E n) := by
        intro v
        by_cases hv : hdist w (v : E n) ≤ hdist w u₀ + 1
        · exact hmin ⟨hv, v.2⟩
        · push_neg at hv
          have h2 := hmin ⟨show hdist w u₀ ≤ hdist w u₀ + 1 from
            le_add_of_nonneg_right zero_le_one, hu₀⟩
          exact le_trans h2 (le_of_lt (lt_trans (lt_add_one _) hv))
      have h3 := hcase u
      have h4 : 1 + 1 / ((k : ℝ) + 1) < hdist w u₁ := by
        simpa [add_comm] using (lt_sub_iff_add_lt.mp hk)
      exact le_trans (le_of_lt h4) h3
    · exact ⟨0, fun u => absurd ⟨u, u.2⟩ hne⟩
  have hsup : (⋃ k : ℕ, {w : E n | ∀ u : ↥Sᶜ, (1 + 1 / ((k : ℝ) + 1)) ≤ hdist w (u : E n)})
      ⊆ {u : E n | NearIdAt b u η} := by
    intro w hw u hu
    rw [Set.mem_iUnion] at hw
    obtain ⟨k, hk⟩ := hw
    by_contra hcon
    have h1 : (1 : ℝ) + 1 / ((k : ℝ) + 1) ≤ hdist w u := hk ⟨u, hcon⟩
    have h2 : (1 : ℝ) < 1 + 1 / ((k : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    exact (not_lt_of_ge hu) (lt_of_lt_of_le h2 h1)
  rw [show {u : E n | NearIdAt b u η}
      = ⋃ k : ℕ, {w : E n | ∀ u : ↥Sᶜ, (1 + 1 / ((k : ℝ) + 1)) ≤ hdist w (u : E n)}
      from le_antisymm hsub hsup]
  exact MeasurableSet.iUnion fun k => (hAcl k).measurableSet

/-! ## 2. Finiteness of the set of conjugates near the identity at a point -/

/-- Free-group algebra behind the injectivity of the conjugation map: if `b` conjugated by the
inverse of `B * A⁻¹` and by the inverse of `B' * A⁻¹` give the same element, then `B' * B⁻¹`
centralises `b`. -/
theorem ftb_conj_eq_imp {G : Type*} [Group G] (b A B B' : G)
    (h : (B * A⁻¹)⁻¹ * b * (B * A⁻¹) = (B' * A⁻¹)⁻¹ * b * (B' * A⁻¹)) :
    (B' * B⁻¹) * b * (B' * B⁻¹)⁻¹ = b := by
  have key : (B' * B⁻¹) * b * (B' * B⁻¹)⁻¹
      = (B' * A⁻¹) * ((B * A⁻¹)⁻¹ * b * (B * A⁻¹)) * (B' * A⁻¹)⁻¹ := by group
  rw [h] at key
  have key2 : (B' * A⁻¹) * ((B' * A⁻¹)⁻¹ * b * (B' * A⁻¹)) * (B' * A⁻¹)⁻¹ = b := by group
  rw [key2] at key
  exact key

/-- For a discrete `Λ` and `b ∈ Λ`, only finitely many `Λ`-conjugates of `b` are `η`-near the
identity at a fixed point `w`. -/
theorem ftb_conjSetFinite {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
    (Λ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Λ))
    (b : PO n 1) (hb : b ∈ Λ) (w : E n) (η : ℝ) :
    {c : PO n 1 | NearIdAt c w η ∧ ∃ γ ∈ Λ, c = γ⁻¹ * b * γ}.Finite := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hsub : {c : PO n 1 | NearIdAt c w η ∧ ∃ γ ∈ Λ, c = γ⁻¹ * b * γ} ⊆
      Subtype.val '' {γ : Λ | hdist w ((γ : PO n 1) • w) ≤ η} := by
    rintro c ⟨hc, γ, hγ, rfl⟩
    have hcΛ : γ⁻¹ * b * γ ∈ Λ := Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hγ) hb) hγ
    refine ⟨⟨γ⁻¹ * b * γ, hcΛ⟩, ?_, rfl⟩
    have h0 : hdist w w ≤ 1 := by
      rw [(hId.eq_zero w w).mpr rfl]
      norm_num
    exact le_of_lt (hc w h0)
  exact ((finite_shortAt n hA hI Λ hdisc w η).image Subtype.val).subset hsub

/-! ## 3. The bad points of the centraliser hull are null -/

/-- **The bad points of the centraliser hull are null.**  No point of the measurable hull
`Es = toMeasurable (volH n) Dc` has a translate by the centraliser `C` of `b` in `Γ`, and a
`Γ`-translate of `z`, such that both `γ • z` and `c • (γ • z)` lie in `Es`. -/
theorem ftb_badSetNull {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ)) (b : PO n 1)
    (Dc : Set (E n))
    (hDc : IsFundamentalDomain ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ) Dc (volH n)) :
    volH n {z : E n | ∃ (γ : Γ) (c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ)),
      c ≠ 1 ∧ (γ : PO n 1) • z ∈ toMeasurable (volH n) Dc ∧
      (c : PO n 1) • ((γ : PO n 1) • z) ∈ toMeasurable (volH n) Dc} = 0 := by
  set Es : Set (E n) := toMeasurable (volH n) Dc with hEs
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := poOneSMul
  have hmul : ∀ (a b' : PO n 1) (u : E n), (a * b') • u = a • (b' • u) := poMulSMul
  letI : MulAction (PO n 1) (E n) := { one_smul := hone, mul_smul := hmul }
  have hEs_ae : Es =ᵐ[volH n] Dc := by
    rw [hEs]; exact hDc.nullMeasurableSet.toMeasurable_ae_eq
  have hdiff : volH n (Es \ Dc) = 0 := (ae_eq_set.mp hEs_ae).1
  have hmp : ∀ g : PO n 1, MeasurePreserving (fun u : E n => g • u) (volH n) (volH n) :=
    (HypIsoData.ofProp hI).measurePreserving_smul
  haveI : SMulInvariantMeasure (PO n 1) (E n) (volH n) :=
    ⟨fun c s hs => (hmp c).measure_preimage hs.nullMeasurableSet⟩
  letI : MulAction ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ) (E n) := inferInstance
  haveI : Countable Γ := countable_of_isDiscrete (PO n 1) hdisc
  haveI : Countable ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ) := by
    have hf : Function.Injective
        (fun c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ) =>
          (⟨(c : PO n 1), c.2.2⟩ : Γ)) := by
      intro a b' hab
      exact Subtype.ext (by simpa using congrArg (fun x : Γ => (x : PO n 1)) hab)
    exact hf.countable
  -- two distinct `C`-translates inside `Dc` are null
  have hpair : ∀ c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ), c ≠ 1 →
      volH n (Dc ∩ (c : PO n 1)⁻¹ • Dc) = 0 := by
    intro c hc
    have h1 := hDc.aedisjoint (show c⁻¹ ≠ (1 : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ))
      from fun h => hc (inv_eq_one.mp h))
    dsimp only [Function.onFun] at h1
    have h2 : (((1 : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ))) • Dc : Set (E n)) = Dc := by
      show (fun x : E n => (1 : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ)) • x) '' Dc = Dc
      rw [show (fun x : E n => (1 : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ)) • x)
          = fun x : E n => x from funext fun x => hone x]
      exact Set.image_id Dc
    rw [h2] at h1
    have h3 : volH n (((c : PO n 1)⁻¹) • Dc ∩ Dc) = 0 := h1
    rw [Set.inter_comm] at h3
    exact h3
  -- the `Dc`-bad points are null
  have hmid : volH n {x : E n | x ∈ Dc ∧ ∃ c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ),
      c ≠ 1 ∧ (c : PO n 1) • x ∈ Dc} = 0 := by
    refine measure_mono_null ?_ (measure_iUnion_null fun c :
      {c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ) // c ≠ 1} => hpair c.1 c.2)
    rintro x ⟨hxD, c, hc, hcx⟩
    refine Set.mem_iUnion.mpr ⟨⟨c, hc⟩, ⟨hxD, ?_⟩⟩
    exact Set.mem_smul_set.mpr ⟨(c : PO n 1) • x, hcx, by
      show (c : PO n 1)⁻¹ • ((c : PO n 1) • x) = x
      rw [← hmul, inv_mul_cancel, hone]⟩
  -- the hull-bad points are null
  have hBadM : volH n {x : E n | x ∈ Es ∧ ∃ c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ),
      c ≠ 1 ∧ (c : PO n 1) • x ∈ Es} = 0 := by
    have hzero : volH n ((Es \ Dc) ∪ ({x : E n | x ∈ Dc ∧
        ∃ c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ), c ≠ 1 ∧ (c : PO n 1) • x ∈ Dc} ∪
        ⋃ c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ),
          (c : PO n 1)⁻¹ • (Es \ Dc))) = 0 := by
      refine measure_union_null hdiff (measure_union_null hmid (measure_iUnion_null fun c => ?_))
      rw [measure_smul]
      exact hdiff
    refine measure_mono_null ?_ hzero
    rintro x ⟨hxEs, c, hc, hcxEs⟩
    by_cases hxDc : x ∈ Dc
    · by_cases hcxDc : (c : PO n 1) • x ∈ Dc
      · exact Or.inr (Or.inl ⟨hxDc, c, hc, hcxDc⟩)
      · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨c, Set.mem_smul_set.mpr
          ⟨(c : PO n 1) • x, ⟨hcxEs, hcxDc⟩, by
            show (c : PO n 1)⁻¹ • ((c : PO n 1) • x) = x
            rw [← hmul, inv_mul_cancel, hone]⟩⟩))
    · exact Or.inl ⟨hxEs, hxDc⟩
  -- assemble
  have hUnion : (volH n) (⋃ γ : Γ, ((γ : PO n 1)⁻¹) • {x : E n | x ∈ Es ∧
      ∃ c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ),
        c ≠ 1 ∧ (c : PO n 1) • x ∈ Es}) = 0 := by
    refine measure_iUnion_null fun γ : Γ => ?_
    rw [measure_smul]
    exact hBadM
  refine measure_mono_null ?_ hUnion
  rintro z ⟨γ, c, hcne, h1, h2⟩
  refine Set.mem_iUnion.mpr ⟨γ, ?_⟩
  rw [Set.mem_inv_smul_set_iff]
  exact ⟨h1, c, hcne, h2⟩

/-! ## 4. The counting bound at a "good" point -/

/-- **Counting bound.** Let `Λ ≤ PO n 1` be discrete, `b ∈ Λ`, `T` a set on which `b` is
`η₁`-near-identity, `Es` a set such that no point of `Es` has a non-trivial translate by the
centraliser of `b` in `Λ` still in `Es`, and suppose that the `Λ`-conjugates of `b` that are
`η₁`-near-identity at a point number at most `Cℓ`.  Then the `Λ`-translates of `z` lying in
`T ∩ Es` number at most `Cℓ`. -/
theorem ftb_countAtGood {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
    (Λ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Λ))
    (b : PO n 1) (hb : b ∈ Λ) (η₁ : ℝ) (Cℓ : ℕ)
    (hCℓ : ∀ w : E n, NearIdAt b w η₁ →
      {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * b * γ}.ncard ≤ Cℓ)
    (T : Set (E n)) (hT : ∀ u ∈ T, NearIdAt b u η₁)
    (Es : Set (E n)) (z : E n)
    (hgood : ∀ (γ : Λ) (c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Λ)),
      c ≠ 1 → (γ : PO n 1) • z ∈ Es → (c : PO n 1) • ((γ : PO n 1) • z) ∉ Es) :
    ∃ s : Finset Λ, s.card ≤ Cℓ ∧
      ∀ γ : Λ, (γ : PO n 1) • z ∈ T ∩ Es → γ ∈ s := by
  classical
  have hmul : ∀ (a b' : PO n 1) (u : E n), (a * b') • u = a • (b' • u) :=
    (POBasic.ofProp hA).mul_smul
  by_cases hSne : ∃ γ : Λ, (γ : PO n 1) • z ∈ T ∩ Es
  · obtain ⟨γ₁, hγ₁⟩ := hSne
    set w : E n := (γ₁ : PO n 1) • z with hw
    have hwT : w ∈ T := by rw [hw]; exact hγ₁.1
    have hwEs : w ∈ Es := by rw [hw]; exact hγ₁.2
    have hAfin : {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * b * γ}.Finite :=
      ftb_conjSetFinite hA hI Λ hdisc b hb w η₁
    have hAcard : {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * b * γ}.ncard ≤ Cℓ :=
      hCℓ w (hT w hwT)
    -- the conjugation map
    set Φ : Λ → PO n 1 :=
      fun γ => ((γ₁ * γ⁻¹ : Λ) : PO n 1) * b * (((γ₁ * γ⁻¹ : Λ) : PO n 1))⁻¹ with hΦdef
    have hΦexp : ∀ γ : Λ, Φ γ
        = (↑(γ * γ₁⁻¹) : PO n 1)⁻¹ * b * (↑(γ * γ₁⁻¹) : PO n 1) := by
      intro γ
      simp only [hΦdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    -- its image lands in the finite set of conjugates
    have hmaps : ∀ γ ∈ ({γ : Λ | (γ : PO n 1) • z ∈ T ∩ Es} : Set Λ),
        Φ γ ∈ {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * b * γ} := by
      intro γ hγ
      have hγ' : (γ : PO n 1) • z ∈ T ∩ Es := hγ
      have hCw : ((γ * γ₁⁻¹ : Λ) : PO n 1) • w = (γ : PO n 1) • z := by
        rw [hw, ← hmul]
        congr 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      refine ⟨?_, ?_⟩
      · rw [hΦexp γ]
        refine (nearIdAt_conj n hA hI (((γ * γ₁⁻¹ : Λ) : PO n 1)) b w η₁).mpr ?_
        rw [hCw]
        exact hT _ hγ'.1
      · refine ⟨γ * γ₁⁻¹, (γ * γ₁⁻¹).2, ?_⟩
        rw [hΦexp γ]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    -- good points have injective conjugation map
    have hinj : Set.InjOn Φ ({γ : Λ | (γ : PO n 1) • z ∈ T ∩ Es} : Set Λ) := by
      intro γ hγ γ' hγ' heq
      have hγ'p : (γ : PO n 1) • z ∈ T ∩ Es := hγ
      have hγ''p : (γ' : PO n 1) • z ∈ T ∩ Es := hγ'
      by_contra hne
      -- the two conjugates agree, hence `γ' * γ⁻¹` centralises `b`
      have hb_eq : (↑(γ * γ₁⁻¹) : PO n 1)⁻¹ * b * (↑(γ * γ₁⁻¹) : PO n 1)
          = (↑(γ' * γ₁⁻¹) : PO n 1)⁻¹ * b * (↑(γ' * γ₁⁻¹) : PO n 1) := by
        rw [← hΦexp γ, ← hΦexp γ', heq]
      have hb_eq' : (((γ : PO n 1) * ((γ₁ : PO n 1))⁻¹)⁻¹ * b *
            ((γ : PO n 1) * ((γ₁ : PO n 1))⁻¹))
          = (((γ' : PO n 1) * ((γ₁ : PO n 1))⁻¹)⁻¹ * b *
            ((γ' : PO n 1) * ((γ₁ : PO n 1))⁻¹)) := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hb_eq
      have hδcomm : ((γ' * γ⁻¹ : Λ) : PO n 1) * b * (((γ' * γ⁻¹ : Λ) : PO n 1))⁻¹ = b := by
        have h3 : ((γ' * γ⁻¹ : Λ) : PO n 1)
            = ((γ' : Λ) : PO n 1) * (((γ : Λ) : PO n 1))⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [h3]
        exact ftb_conj_eq_imp b (((γ₁ : Λ) : PO n 1)) (((γ : Λ) : PO n 1))
          (((γ' : Λ) : PO n 1)) hb_eq'
      have hcent : ((γ' * γ⁻¹ : Λ) : PO n 1)
          ∈ Subgroup.centralizer ({b} : Set (PO n 1)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        have h4 := congrArg (fun t => t * (((γ' * γ⁻¹ : Λ) : PO n 1))) hδcomm
        have h6 : ((γ' * γ⁻¹ : Λ) : PO n 1) * b = b * ((γ' * γ⁻¹ : Λ) : PO n 1) := by
          simpa only [mul_assoc, inv_mul_cancel, mul_one] using h4
        exact h6.symm
      have hδne : (γ' * γ⁻¹ : Λ) ≠ 1 := by
        intro h1'
        exact hne (mul_inv_eq_one.mp h1').symm
      set c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Λ) :=
        ⟨((γ' * γ⁻¹ : Λ) : PO n 1), hcent, (γ' * γ⁻¹ : Λ).2⟩ with hcdef
      have hcne : c ≠ 1 := by
        intro h1'
        have h2' : ((γ' * γ⁻¹ : Λ) : PO n 1) = (1 : PO n 1) := by
          have h3' := congrArg
            (fun t : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Λ) => (t : PO n 1)) h1'
          simpa [hcdef] using h3'
        exact hδne (Subtype.ext h2')
      have hcoeeq : (c : PO n 1) = ((γ' * γ⁻¹ : Λ) : PO n 1) := rfl
      have hγ'eq : (γ' : PO n 1) = (c : PO n 1) * (γ : PO n 1) := by
        rw [hcoeeq]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hmem : (c : PO n 1) • ((γ : PO n 1) • z) ∈ Es := by
        have h1' : (c : PO n 1) • ((γ : PO n 1) • z) = (γ' : PO n 1) • z := by
          rw [← hmul, ← hγ'eq]
        rw [h1']
        exact hγ''p.2
      exact hgood γ c hcne hγ'p.2 hmem
    have hSfin : ({γ : Λ | (γ : PO n 1) • z ∈ T ∩ Es} : Set Λ).Finite := by
      refine Set.Finite.of_finite_image (hAfin.subset ?_) hinj
      rintro _ ⟨γ, hγ, rfl⟩
      exact hmaps γ hγ
    refine ⟨hSfin.toFinset, ?_, ?_⟩
    · have h1 : hSfin.toFinset.card
          = ({γ : Λ | (γ : PO n 1) • z ∈ T ∩ Es} : Set Λ).ncard :=
        (Set.ncard_eq_toFinset_card _ hSfin).symm
      rw [h1]
      exact le_trans (Set.ncard_le_ncard_of_injOn Φ hmaps hinj hAfin) hAcard
    · intro γ hγ
      exact hSfin.mem_toFinset.mpr hγ
  · exact ⟨∅, by simp, fun γ hγ => absurd ⟨γ, hγ⟩ hSne⟩

/-! ## 5. The main theorem -/

/-- **Unfolding the tube at a stratum, general dimension.**  `Λ` discrete, `D` a fundamental domain of `Λ`, `Dc` a fundamental domain of the centraliser `C = centralizer {b} ⊓ Λ`.  `Cℓ` bounds the number of conjugates of `b` by elements of `Λ` that are simultaneously `η₁`-near-identity at a common point `w` at which `b` is `η₁`-near-identity (the conjCount pigeonhole).  Conclusion: `{u | NearIdAt b u η₁}` has, inside `Dc`, measure at most `Cℓ · volH D`.  The `n = 3` case is PROVED in `Submission/Work/Mostow/gapA/unfoldTube.lean` (`Work.Mostow.gapA.unfoldTube`, `hconj` in place of the `Cℓ` hypothesis, constant `2`) and is the template. -/
theorem ftbUnfold (j m : ℕ) (hAj : Submission.Mostow.POActionProp j)
    (hIj : Submission.Mostow.HypIsometryProp j)
    (hA : Submission.Mostow.POActionProp (j + m)) (hI : Submission.Mostow.HypIsometryProp (j + m)) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ (Λ : Subgroup (PO (j + m) 1)) (D Dc : Set (E (j + m)))
      (b : PO (j + m) 1) (Cℓ : ℕ),
      IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (j + m)) → b ∈ Λ →
      IsFundamentalDomain ↥(Subgroup.centralizer ({b} : Set (PO (j + m) 1)) ⊓ Λ) Dc (volH (j + m)) →
      (∀ w : E (j + m), NearIdAt b w η₁ →
        {c : PO (j + m) 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * b * γ}.ncard ≤ Cℓ) →
      volH (j + m) ({u : E (j + m) | NearIdAt b u η₁} ∩ Dc)
        ≤ (Cℓ : ENNReal) * volH (j + m) D := by
  refine ⟨1, one_pos, ?_⟩
  intro Λ D Dc b Cℓ hdisc hD hb hDc hCℓ
  -- the measurable hull of the centraliser fundamental domain
  set Es : Set (E (j + m)) := toMeasurable (volH (j + m)) Dc with hEs
  have hEmeas : MeasurableSet Es := by
    rw [hEs]; exact measurableSet_toMeasurable _ _
  have hEae : Es =ᵐ[volH (j + m)] Dc := by
    rw [hEs]; exact hDc.nullMeasurableSet.toMeasurable_ae_eq
  -- the bad set is null
  have hBadNull := ftb_badSetNull hA hI Λ hdisc b Dc hDc
  have hBadNull' : volH (j + m) {z : E (j + m) | ∃ (γ : Λ)
      (c : ↥(Subgroup.centralizer ({b} : Set (PO (j + m) 1)) ⊓ Λ)),
        c ≠ 1 ∧ (γ : PO (j + m) 1) • z ∈ Es ∧
          (c : PO (j + m) 1) • ((γ : PO (j + m) 1) • z) ∈ Es} = 0 := by
    rw [hEs]
    exact hBadNull
  -- the counting hypothesis
  have hcount : ∀ᵐ z ∂((volH (j + m)).restrict D), ∃ s : Finset Λ, s.card ≤ Cℓ ∧
      ∀ γ : Λ, (γ : PO (j + m) 1) • z ∈ {u : E (j + m) | NearIdAt b u 1} ∩ Es → γ ∈ s := by
    rw [ae_restrict_iff'₀ hD.nullMeasurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBadNull'] with z hz hzD
    refine ftb_countAtGood hA hI Λ hdisc b hb 1 Cℓ hCℓ
      {u : E (j + m) | NearIdAt b u 1} (fun u hu => hu) Es z ?_
    intro γ c hcne hγEs hcontra
    exact hz ⟨γ, c, hcne, hγEs, hcontra⟩
  -- assemble
  have hFmeas : MeasurableSet ({u : E (j + m) | NearIdAt b u 1} ∩ Es) :=
    (ftbMeasurableSetNearId (j + m) hA hI b 1).inter hEmeas
  have hvol_eq : volH (j + m) ({u : E (j + m) | NearIdAt b u 1} ∩ Dc)
      = volH (j + m) ({u : E (j + m) | NearIdAt b u 1} ∩ Es) :=
    measure_congr (ae_eq_set_inter (ae_eq_refl _) hEae.symm)
  have hmain := volH_le_card_mul_of_ae_count (j + m) hA hI Λ hdisc (D := D)
    (F := {u : E (j + m) | NearIdAt b u 1} ∩ Es) hD hFmeas Cℓ hcount
  rw [hvol_eq]
  exact hmain

end

end Work.Mostow
