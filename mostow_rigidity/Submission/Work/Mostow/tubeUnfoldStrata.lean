import Mathlib
import Submission.Work.Mostow.tube_nearId
import Submission.Work.Mostow.volH_le_card_mul_of_ae_count
import Submission.Work.Mostow.disp_blk
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.finite_shortAt
import Submission.Work.Mostow.HaarBase

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-! ## Auxiliary lemmas -/

/-- `nrmC k m` is continuous (coordinate projection followed by `PiLp.toLp`). -/
theorem tu_continuous_nrmC (k m : ℕ) : Continuous (nrmC k m) := by
  have hmid : Continuous (fun g : Fin (k + m) → ℝ => fun i : Fin m => g (Fin.natAdd k i)) :=
    continuous_pi fun i => continuous_apply (Fin.natAdd k i)
  have hof : Continuous (WithLp.ofLp : E (k + m) → (Fin (k + m) → ℝ)) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin (k + m) => ℝ)
  have hto : Continuous (WithLp.toLp 2 : (Fin m → ℝ) → E m) :=
    PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)
  rw [show nrmC k m = (WithLp.toLp 2 : (Fin m → ℝ) → E m) ∘
      (fun g : Fin (k + m) → ℝ => fun i : Fin m => g (Fin.natAdd k i)) ∘
      (WithLp.ofLp : E (k + m) → (Fin (k + m) → ℝ)) from rfl]
  exact hto.comp (hmid.comp hof)

/-- The Fermi tube about the standard stratum is closed, hence measurable. -/
theorem tu_isClosed_tube (k m : ℕ) (ρ : ℝ) : IsClosed (tube k m ρ) := by
  have hset : tube k m ρ = {u : E (k + m) | ‖nrmC k m u‖ ≤ Real.sinh ρ} := rfl
  rw [hset]
  exact isClosed_le (continuous_norm.comp (tu_continuous_nrmC k m)) continuous_const

/-- **Conjugation covariance of `NearIdAt`**: conjugating the isometry and translating the base
point by the same element does not change near-identity. -/
theorem tu_nearIdAt_conj {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
    (C γ : PO n 1) (u : E n) (η : ℝ) :
    NearIdAt (C⁻¹ * γ * C) u η ↔ NearIdAt γ (C • u) η := by
  have hone : ∀ v : E n, (1 : PO n 1) • v = v := (POBasic.ofProp hA).one_smul
  have hmul : ∀ (g h : PO n 1) (v : E n), (g * h) • v = g • (h • v) :=
    (POBasic.ofProp hA).mul_smul
  have hisom : ∀ (g : PO n 1) (v w : E n), hdist (g • v) (g • w) = hdist v w :=
    (HypIsoData.ofProp hI).isom_smul
  have hCin : ∀ v : E n, C • (C⁻¹ • v) = v := by
    intro v
    rw [← hmul C C⁻¹ v, mul_inv_cancel, hone]
  have hconj : ∀ v : E n, (C⁻¹ * γ * C) • v = C⁻¹ • (γ • (C • v)) := by
    intro v
    rw [hmul (C⁻¹ * γ) C v, hmul C⁻¹ γ (C • v)]
  constructor
  · intro h v hv
    have hv' : hdist u (C⁻¹ • v) ≤ 1 := by
      have h1 : hdist u (C⁻¹ • v) = hdist (C • u) v := by
        rw [← hisom C u (C⁻¹ • v), hCin v]
      rw [h1]; exact hv
    have h2 := h (C⁻¹ • v) hv'
    rw [hconj (C⁻¹ • v), hCin v] at h2
    have h3 : hdist (C⁻¹ • v) (C⁻¹ • (γ • v)) = hdist v (γ • v) := by
      rw [← hisom C (C⁻¹ • v) (C⁻¹ • (γ • v)), hCin v, hCin (γ • v)]
    rw [← h3]
    exact h2
  · intro h v hv
    have hv' : hdist (C • u) (C • v) ≤ 1 := by
      rw [hisom C u v]; exact hv
    have h2 := h (C • v) hv'
    have h3 : hdist v ((C⁻¹ * γ * C) • v) = hdist (C • v) (γ • (C • v)) := by
      rw [hconj v]
      rw [← hisom C v (C⁻¹ • (γ • (C • v))), hCin (γ • (C • v))]
    rw [h3]
    exact h2

/-- Free-group algebra behind the injectivity of the conjugation map: if `b` conjugated by the
inverse of `B * A⁻¹` and by the inverse of `B' * A⁻¹` give the same element, then `B' * B⁻¹`
centralises `b`. -/
theorem tu_conj_eq_imp {G : Type*} [Group G] (b A B B' : G)
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
theorem tu_conjSetFinite {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
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

/-- **The bad points of the centraliser hull are null.**  No point of the measurable hull
`Es = toMeasurable (volH n) Dc` has a translate by the centraliser `C` of `b` in `Γ`, and a `Γ`-translate
of `z`, such that both `γ • z` and `c • (γ • z)` lie in `Es`. -/
theorem tu_badSetNull {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
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
      {c : ↥(Subgroup.centralizer ({b} : Set (PO n 1)) ⊓ Γ) // c ≠ 1} => hpair c c.2)
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

/-! ## The counting bound at a "good" point -/

/-- **Counting bound.** Let `Λ ≤ PO n 1` be discrete, `b ∈ Λ`, `T` a set on which `b` is
`η₁`-near-identity, `Es` a set such that no point of `Es` has a non-trivial translate by the
centraliser of `b` in `Λ` still in `Es`, and suppose that the `Λ`-conjugates of `b` that are
`η₁`-near-identity at a point number at most `Cℓ`.  Then the `Λ`-translates of `z` lying in
`T ∩ Es` number at most `Cℓ`. -/
theorem tu_countAtGood {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
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
      tu_conjSetFinite hA hI Λ hdisc b hb w η₁
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
        refine (tu_nearIdAt_conj hA hI (((γ * γ₁⁻¹ : Λ) : PO n 1)) b w η₁).mpr ?_
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
        exact tu_conj_eq_imp b (((γ₁ : Λ) : PO n 1)) (((γ : Λ) : PO n 1))
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

/-! ## The main theorem -/

/-! **(I) of the strata chapter: the Fermi tube unfolded over the centraliser.**

Setting: `Λ ≤ PO (j+m) 1` discrete with fundamental domain `D`, `b = blk j m 1 R ∈ Λ` with `R`
having no fixed vector, `C := Subgroup.centralizer {b} ⊓ Λ`, and `Dc` a fundamental domain of `C`.
The Fermi tube `tube j m ρ` of radius `ρ` about the standard stratum is contained in the short
set `Tb := {w | NearIdAt b w η₁}` of `b` (this is `Work.Mostow.tube_nearId`, already PROVED:
`0 ≤ ρ`, `0 < η`, `2 * sinh (ρ+1) * rotN R ≤ η` imply `u ∈ tube j m ρ → NearIdAt (blk j m 1 R) u η`).

Route.  For almost every `z ∈ D`, let `S z = {γ : Λ // (γ : PO (j+m) 1) • z ∈ tube j m ρ ∩ Dc}`.
Pick `γ₁ ∈ S z` (if any) and put `w = (γ₁ : PO (j+m) 1) • z`.  Then `b` is `η₁`-near-identity at
`w` (by `tube_nearId`), and for `γ ∈ S z` the conjugate
`γ₁ * (γ⁻¹ * b * γ) * γ₁⁻¹ = (γ * γ₁⁻¹)⁻¹ * b * (γ * γ₁⁻¹)` is again `η₁`-near-identity at `w`
(NearIdAt is conjugation-covariant: `NearIdAt (C⁻¹ * g * C) u η ↔ NearIdAt g (C • u) η`, a
10-line computation from the action laws).  The hypothesis bounds the set of `Λ`-conjugates of
`b` that are near-identity at `w` by `Cℓ`, so two elements of `S z` with the same conjugate differ
by an element of `C`; since `Dc` is a `C`-fundamental domain, two `C`-equivalent points of a
measurable hull of `Dc` are equal almost everywhere (replace `Dc` by its `toMeasurable` hull and
argue as in `Work.Mostow.gapA.badSet_null`), and `γ • z = γ' • z` forces `γ = γ'` off the fixed
set of `γ'⁻¹ * γ` (a null set).  Hence `S z` is contained in a finite set of cardinality `≤ Cℓ`
for a.e. `z ∈ D`, and `Work.Mostow.volH_le_card_mul_of_ae_count` (group `Λ`, fundamental domain
`D`, measurable set `tube j m ρ ∩ Dc`, `N = Cℓ`) gives the conclusion.

`η₁ := 1` (or any positive number) works: only `ρ ≥ 1` and the explicit bound
`2 * sinh (ρ+1) * rotN R ≤ η₁` are used. -/
theorem tubeUnfoldStrata (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j) (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m)) : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ (Λ : Subgroup (PO (j + m) 1)) (D : Set (E (j + m))), IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (j + m)) → ∀ R : E m ≃ₗᵢ[ℝ] E m, blk j m 1 R ∈ Λ → (∀ w, R w = w → w = 0) → ∀ (Dc : Set (E (j + m))), IsFundamentalDomain (↑(Subgroup.centralizer {blk j m 1 R} ⊓ Λ : Subgroup (PO (j + m) 1))) Dc (volH (j + m)) → ∀ (Cℓ : ℕ), (∀ w : E (j + m), NearIdAt (blk j m 1 R) w η₁ → {c : PO (j + m) 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Λ, c = γ⁻¹ * blk j m 1 R * γ}.ncard ≤ Cℓ) → ∀ ρ : ℝ, 1 ≤ ρ → 2 * Real.sinh (ρ + 1) * rotN R ≤ η₁ → volH (j + m) (tube j m ρ ∩ Dc) ≤ (Cℓ : ENNReal) * volH (j + m) D := by
  refine ⟨1, one_pos, ?_⟩
  intro Λ D hdisc hD R hb hRfix Dc hDc Cℓ hCℓ ρ hρ1 hρbnd
  -- the measurable hull of the centraliser fundamental domain
  set Es : Set (E (j + m)) := toMeasurable (volH (j + m)) Dc with hEs
  have hEmeas : MeasurableSet Es := by
    rw [hEs]; exact measurableSet_toMeasurable _ _
  have hEae : Es =ᵐ[volH (j + m)] Dc := by
    rw [hEs]; exact hDc.nullMeasurableSet.toMeasurable_ae_eq
  -- the bad set is null
  have hBadNull := tu_badSetNull hA hI Λ hdisc (blk j m 1 R) Dc hDc
  have hBadNull' : volH (j + m) {z : E (j + m) | ∃ (γ : Λ)
      (c : ↥(Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ⊓ Λ)),
        c ≠ 1 ∧ (γ : PO (j + m) 1) • z ∈ Es ∧
          (c : PO (j + m) 1) • ((γ : PO (j + m) 1) • z) ∈ Es} = 0 := by
    rw [hEs]
    exact hBadNull
  -- the counting hypothesis
  have hcount : ∀ᵐ z ∂((volH (j + m)).restrict D), ∃ s : Finset Λ, s.card ≤ Cℓ ∧
      ∀ γ : Λ, (γ : PO (j + m) 1) • z ∈ tube j m ρ ∩ Es → γ ∈ s := by
    rw [ae_restrict_iff'₀ hD.nullMeasurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBadNull'] with z hz hzD
    refine tu_countAtGood hA hI Λ hdisc (blk j m 1 R) hb 1 Cℓ hCℓ (tube j m ρ) ?_ Es z ?_
    · intro u hu
      exact tube_nearId j m hAj hIj hA hI R ρ 1 (by linarith) one_pos hρbnd u hu
    · intro γ c hcne hγEs hcontra
      exact hz ⟨γ, c, hcne, hγEs, hcontra⟩
  -- assemble
  have hFmeas : MeasurableSet (tube j m ρ ∩ Es) :=
    (tu_isClosed_tube j m ρ).measurableSet.inter hEmeas
  have hvol_eq : volH (j + m) (tube j m ρ ∩ Dc) = volH (j + m) (tube j m ρ ∩ Es) :=
    measure_congr (ae_eq_set_inter (ae_eq_refl _) hEae.symm)
  have hmain := volH_le_card_mul_of_ae_count (j + m) hA hI Λ hdisc (D := D)
    (F := tube j m ρ ∩ Es) hD hFmeas Cℓ hcount
  rw [hvol_eq]
  exact hmain

end

end Work.Mostow
