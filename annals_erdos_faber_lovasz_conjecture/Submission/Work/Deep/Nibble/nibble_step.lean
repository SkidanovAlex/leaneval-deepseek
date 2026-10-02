import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.nibble_defs
import Submission.Work.Deep.Nibble.nibble_round2
import Submission.Work.Deep.Nibble.nibble_state
import Submission.Work.Deep.Nibble.nibble_round_lemmas

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Nibble

variable {n : ℕ}

/-- The expected level of the residual degrees after one round. -/
noncomputable def rPred (r : ℕ) (θ : ℝ) (D : ℕ) : ℝ :=
  (D : ℝ) * (1 - θ / (D : ℝ)) ^ ((r - 1) * (D - 1))

/-- The level after one round: `rPred` with a margin `(1-3ε')` so that the new level is a
lower bound for the residual degrees. -/
noncomputable def nextD (r : ℕ) (θ : ℝ) (D : ℕ) (ε' : ℝ) : ℕ := ⌈(1 - 3 * ε') * rPred r θ D⌉₊

/-- The uncovered vertex set after one round with outcome `ω`. -/
noncomputable def rU' (𝓗 : Set (Set (Fin n))) (U : Set (Fin n)) (ω : res 𝓗 U → Bool) :
    Set (Fin n) :=
  {x : Fin n | ∃ v : ↥U, v ∉ covX (res 𝓗 U) ω ∧ (v : Fin n) = x}

/-- The matching of isolated kept edges of one round, as edges of `𝓗`. -/
noncomputable def rM (𝓗 : Set (Set (Fin n))) (U : Set (Fin n)) (ω : res 𝓗 U → Bool) :
    Set (Set (Fin n)) :=
  {s : Set (Fin n) | ∃ e : res 𝓗 U, e ∈ isoFam (res 𝓗 U) ω ∧
    (Subtype.val '' (e : Set ↥U) : Set (Fin n)) = s}

variable {𝓗 : Set (Set (Fin n))} {U : Set (Fin n)} {ω : res 𝓗 U → Bool} {V W : Type*}

theorem mem_image_iff' (f : V → W) {s : Set V} {x : W} : x ∈ f '' s ↔ ∃ y ∈ s, f y = x := by
  constructor
  · rintro ⟨y, hy, h⟩; exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩; exact ⟨y, hy, h⟩

theorem mem_rU' {x : Fin n} :
    x ∈ rU' 𝓗 U ω ↔ ∃ v : ↥U, v ∉ covX (res 𝓗 U) ω ∧ (v : Fin n) = x := Iff.rfl

theorem mem_rM {s : Set (Fin n)} :
    s ∈ rM 𝓗 U ω ↔ ∃ e : res 𝓗 U, e ∈ isoFam (res 𝓗 U) ω ∧
      (Subtype.val '' (e : Set ↥U) : Set (Fin n)) = s := Iff.rfl

theorem rU'_eq : rU' 𝓗 U ω = Subtype.val '' (residV (res 𝓗 U) ω) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩

theorem rU'_sub : rU' 𝓗 U ω = U \ (Subtype.val '' (covX (res 𝓗 U) ω)) := by
  rw [rU'_eq]; exact (round_state 𝓗 U ω).1

theorem rU'_card : (rU' 𝓗 U ω).ncard + (covX (res 𝓗 U) ω).ncard = U.ncard := by
  rw [rU'_eq]; exact (round_state 𝓗 U ω).2.1

theorem rU'_hd (v : ↥U) (hv : v ∈ residV (res 𝓗 U) ω) :
    hd (res 𝓗 (rU' 𝓗 U ω)) ⟨(v : Fin n), ⟨v, hv, rfl⟩⟩ = hd (residH (res 𝓗 U) ω) v :=
  (round_state 𝓗 U ω).2.2.2 v hv

theorem rM_sub : rM 𝓗 U ω ⊆ 𝓗 := by
  intro s hs
  obtain ⟨e, heIso, hes⟩ := mem_rM.mp hs
  rw [← hes]
  exact e.2

theorem rM_uni {r : ℕ} (hu : HUnif 𝓗 r) : ∀ e ∈ rM 𝓗 U ω, e.ncard = r := by
  intro s hs
  obtain ⟨e, heIso, hes⟩ := mem_rM.mp hs
  rw [← hes, ncard_valn]
  exact res_unif hu (e : Set ↥U) e.2

theorem rM_disj {r : ℕ} (hu : HUnif 𝓗 r) : ∀ e ∈ rM 𝓗 U ω, ∀ f ∈ rM 𝓗 U ω, e ≠ f → Disjoint e f := by
  haveI : Fintype ↥U := Fintype.ofFinite ↥U
  intro s hs t ht hst
  obtain ⟨e, heIso, hes⟩ := mem_rM.mp hs
  obtain ⟨f, hfIso, hfs⟩ := mem_rM.mp ht
  have hef : e ≠ f := by
    intro hc
    exact hst (by rw [← hes, ← hfs, hc])
  have hd := (isofam_matching (res 𝓗 U) ω (res_unif hu)).1 e f heIso hfIso hef
  rw [← hes, ← hfs]
  refine Set.disjoint_left.mpr ?_
  intro x hxe hxf
  obtain ⟨y, hy, hyx⟩ := mem_image_iff' _ |>.mp hxe
  obtain ⟨z, hz, hzx⟩ := mem_image_iff' _ |>.mp hxf
  have hyz : y = z := Subtype.val_injective (by rw [hyx, hzx])
  exact (Set.disjoint_left.mp hd) hy (hyz ▸ hz)

theorem rM_sub_U' : ⋃₀ rM 𝓗 U ω ⊆ U \ rU' 𝓗 U ω := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := Set.mem_sUnion.mp hx
  obtain ⟨e, heIso, hes⟩ := mem_rM.mp hs
  rw [← hes] at hsx
  obtain ⟨y, hy, hyx⟩ := mem_image_iff' _ |>.mp hsx
  have hyc : y ∈ covX (res 𝓗 U) ω := Set.mem_biUnion ⟨e.2, heIso.1⟩ hy
  rw [rU'_sub]
  refine ⟨?_, ?_⟩
  · rw [← hyx]; exact y.2
  · intro hmem
    exact hmem.2 ⟨y, hyc, hyx⟩

theorem rU'_subset : rU' 𝓗 U ω ⊆ U := by
  rw [rU'_sub]; exact Set.sdiff_subset

theorem mem_biUnion_iff' {α : Type*} {ι : Sort*} {p : ι → Prop} {f : ι → Set α} {x : α} :
    x ∈ (⋃ i, ⋃ (_ : p i), f i) ↔ ∃ i, p i ∧ x ∈ f i := by
  simp only [Set.mem_iUnion, exists_prop]

/-- One round of the nibble, stated in terms of the uncovered vertex set. -/
theorem nibble_step {r : ℕ} (hr : 2 ≤ r) {θ δ ε ε' : ℝ} {Dmin : ℕ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100)
    (hε0 : 0 < ε) (hε1 : ε ≤ θ / 100) (hεδ : 4 * ε ≤ δ)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 2) (hε'2 : 100 * (ε + ε * (r : ℝ) * θ) ≤ ε')
    {n : ℕ} {𝓗 : Set (Set (Fin n))} {U : Set (Fin n)} {D : ℕ}
    (hDmin1 : 1 ≤ Dmin) (hDmin : Dmin ≤ D)
    (hround : ∀ {V : Type} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) (D' : ℕ),
        Dmin ≤ D' → D' ≤ Fintype.card V → HLin 𝓖 → HUnif 𝓖 r →
        (∀ v : V, |((hd 𝓖 v : ℝ)) - (D' : ℝ)| ≤ ε * (D' : ℝ)) →
        ∃ ω : 𝓖 → Bool, RoundGood 𝓖 r D' θ δ ε' (rPred r θ D') ω)
    (hl : HLin 𝓗) (hu : HUnif 𝓗 r)
    (hDcard : D ≤ U.ncard)
    (hIa : ∀ v ∈ U, (deg 𝓗 U v : ℝ) ≤ (1 + ε) * (D : ℝ))
    (hIb : ∀ v ∈ U, (D : ℝ) ≤ (deg 𝓗 U v : ℝ))
    (hbig : 1 ≤ ε' * rPred r θ D)
    (hε'six : ε' ≤ 1 / 6) :
    ∃ ω : res 𝓗 U → Bool,
       rU' 𝓗 U ω ⊆ U ∧
       (∀ v ∈ rU' 𝓗 U ω, (deg 𝓗 (rU' 𝓗 U ω) v : ℝ) ≤ (1 + 8 * ε') * (nextD r θ D ε' : ℝ)) ∧
       (∀ v ∈ rU' 𝓗 U ω, (nextD r θ D ε' : ℝ) ≤ (deg 𝓗 (rU' 𝓗 U ω) v : ℝ)) ∧
       ((rU' 𝓗 U ω).ncard : ℝ) ≤ (1 + 2 * δ) * Real.exp (-θ) * (U.ncard : ℝ) ∧
       ((U \ (rU' 𝓗 U ω ∪ ⋃₀ rM 𝓗 U ω)).ncard : ℝ) ≤
         r * (1 + δ) * (θ - θ * Real.exp (-θ)) * (U.ncard : ℝ) ∧
       rM 𝓗 U ω ⊆ 𝓗 ∧ (∀ e ∈ rM 𝓗 U ω, e.ncard = r) ∧
       (∀ e ∈ rM 𝓗 U ω, ∀ f ∈ rM 𝓗 U ω, e ≠ f → Disjoint e f) ∧
       (⋃₀ rM 𝓗 U ω) ⊆ U \ rU' 𝓗 U ω := by
  classical
  haveI : Fintype ↥U := Fintype.ofFinite ↥U
  have hPg : U.ncard = Fintype.card ↥U :=
    (Set.ncard_coe U).symm.trans ((Set.ncard_univ (α := ↥U)).trans Nat.card_eq_fintype_card)
  have hDpos : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hDmin1.trans hDmin
  have hpred0 : (0:ℝ) ≤ rPred r θ D := by
    have hDN : (0:ℝ) < (D:ℝ) := by
      have : 0 < D := by omega
      exact_mod_cast this
    rw [rPred]
    refine mul_nonneg (Nat.cast_nonneg D) (pow_nonneg ?_ _)
    rw [sub_nonneg, div_le_one hDN]
    linarith [hθ1, hDpos]
  have hdegle : ∀ v : ↥U, |((hd (res 𝓗 U) v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ) := by
    intro v
    have h1 : hd (res 𝓗 U) v = deg 𝓗 U (v : Fin n) := hd_res_eq_deg 𝓗 U v
    have h2 := hIb (v : Fin n) v.2
    have h3 : (deg 𝓗 U (v : Fin n) : ℝ) ≤ (D : ℝ) + ε * (D : ℝ) := by
      nlinarith [hIa (v : Fin n) v.2]
    have h4 : (0:ℝ) ≤ ε * (D:ℝ) := mul_nonneg (le_of_lt hε0) (Nat.cast_nonneg D)
    rw [h1]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨ω, hω⟩ := hround (V := ↥U) (res 𝓗 U) D hDmin (by rw [← hPg]; exact hDcard)
    (res_linear hl) (res_unif hu) hdegle
  obtain ⟨hcl1, hcl2, hcl3, hcl4⟩ := hω
  have hexp1 : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp2 : (1:ℝ)/2 ≤ Real.exp (-θ) := by
    have h := Real.add_one_le_exp (-θ)
    linarith
  have hnext : nextD r θ D ε' = ⌈(1 - 3 * ε') * rPred r θ D⌉₊ := rfl
  refine ⟨ω, rU'_subset, ?_, ?_, ?_, ?_, rM_sub, rM_uni hu, rM_disj hu, rM_sub_U'⟩
  · -- upper degree bound
    intro v hv
    obtain ⟨y, hy, hyv⟩ := mem_rU'.mp hv
    have hext : (⟨(v : Fin n), hv⟩ : ↥(rU' 𝓗 U ω)) = ⟨(y : Fin n), ⟨y, hy, rfl⟩⟩ :=
      Subtype.ext hyv.symm
    have h1 : hd (res 𝓗 (rU' 𝓗 U ω)) ⟨(v : Fin n), hv⟩ = hd (residH (res 𝓗 U) ω) y := by
      rw [hext, rU'_hd y hy]
    have h2 : |((hd (residH (res 𝓗 U) ω) y : ℝ)) - rPred r θ D| ≤ ε' * rPred r θ D := hcl4 y hy
    have h3 : (deg 𝓗 (rU' 𝓗 U ω) v : ℝ) ≤ (1 + ε') * rPred r θ D := by
      rw [← hd_res_eq_deg 𝓗 (rU' 𝓗 U ω) ⟨v, hv⟩, h1]
      linarith [(abs_le.mp h2).2]
    have h4 : rPred r θ D ≤ (nextD r θ D ε' : ℝ) / (1 - 3 * ε') := by
      have h5 : rPred r θ D * (1 - 3 * ε') ≤ (nextD r θ D ε' : ℝ) := by
        rw [hnext]
        have h6 := Nat.le_ceil ((1 - 3 * ε') * rPred r θ D)
        linarith
      rw [le_div_iff₀ (by linarith)]
      linarith
    have h6 : (1 + ε') / (1 - 3 * ε') ≤ 1 + 8 * ε' := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hε'0, hε'six]
    calc (deg 𝓗 (rU' 𝓗 U ω) v : ℝ) ≤ (1 + ε') * rPred r θ D := h3
      _ ≤ (1 + ε') * ((nextD r θ D ε' : ℝ) / (1 - 3 * ε')) :=
            mul_le_mul_of_nonneg_left h4 (by linarith)
      _ = ((1 + ε') / (1 - 3 * ε')) * (nextD r θ D ε' : ℝ) := by ring
      _ ≤ (1 + 8 * ε') * (nextD r θ D ε' : ℝ) :=
            mul_le_mul_of_nonneg_right h6 (Nat.cast_nonneg _)
  · -- lower degree bound
    intro v hv
    obtain ⟨y, hy, hyv⟩ := mem_rU'.mp hv
    have hext : (⟨(v : Fin n), hv⟩ : ↥(rU' 𝓗 U ω)) = ⟨(y : Fin n), ⟨y, hy, rfl⟩⟩ :=
      Subtype.ext hyv.symm
    have h1 : hd (res 𝓗 (rU' 𝓗 U ω)) ⟨(v : Fin n), hv⟩ = hd (residH (res 𝓗 U) ω) y := by
      rw [hext, rU'_hd y hy]
    have h2 : |((hd (residH (res 𝓗 U) ω) y : ℝ)) - rPred r θ D| ≤ ε' * rPred r θ D := hcl4 y hy
    have h3 : (1 - ε') * rPred r θ D ≤ (deg 𝓗 (rU' 𝓗 U ω) v : ℝ) := by
      rw [← hd_res_eq_deg 𝓗 (rU' 𝓗 U ω) ⟨v, hv⟩, h1]
      linarith [(abs_le.mp h2).1]
    have h4 : (nextD r θ D ε' : ℝ) ≤ (1 - 3 * ε') * rPred r θ D + 1 := by
      rw [hnext]
      have h6 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (1 - 3 * ε') * rPred r θ D from
        mul_nonneg (by linarith) hpred0)
      linarith
    have h5 : (1 : ℝ) ≤ ε' * rPred r θ D := hbig
    have h6 : (1 - 3 * ε') * rPred r θ D + ε' * rPred r θ D ≤ (1 - ε') * rPred r θ D := by
      ring_nf; linarith
    calc (nextD r θ D ε' : ℝ) ≤ (1 - 3 * ε') * rPred r θ D + 1 := h4
      _ ≤ (1 - 3 * ε') * rPred r θ D + ε' * rPred r θ D := by linarith
      _ ≤ (1 - ε') * rPred r θ D := h6
      _ ≤ (deg 𝓗 (rU' 𝓗 U ω) v : ℝ) := h3
  · -- residual size
    have h1 : ((rU' 𝓗 U ω).ncard : ℝ) = (U.ncard : ℝ) - ((covX (res 𝓗 U) ω).ncard : ℝ) := by
      have h2 : ((rU' 𝓗 U ω).ncard : ℝ) + ((covX (res 𝓗 U) ω).ncard : ℝ) = (U.ncard : ℝ) := by
        exact_mod_cast rU'_card
      linarith
    have h2 : ((covX (res 𝓗 U) ω).ncard : ℝ) ≥
        (1 - Real.exp (-θ)) * (U.ncard : ℝ) - δ * (U.ncard : ℝ) := by
      have h3 : |(((covX (res 𝓗 U) ω).ncard : ℝ)) - (1 - Real.exp (-θ)) * (Fintype.card ↥U : ℝ)|
          ≤ δ * (Fintype.card ↥U : ℝ) := hcl2
      have h4 := (abs_le.mp h3).1
      rw [← hPg] at h4
      linarith
    calc ((rU' 𝓗 U ω).ncard : ℝ) = (U.ncard : ℝ) - ((covX (res 𝓗 U) ω).ncard : ℝ) := h1
      _ ≤ (U.ncard : ℝ) - ((1 - Real.exp (-θ)) * (U.ncard : ℝ) - δ * (U.ncard : ℝ)) := by
          nlinarith [h2]
      _ = (Real.exp (-θ) + δ) * (U.ncard : ℝ) := by ring
      _ ≤ (1 + 2 * δ) * Real.exp (-θ) * (U.ncard : ℝ) := by
          have h5 : Real.exp (-θ) + δ ≤ (1 + 2 * δ) * Real.exp (-θ) := by
            nlinarith [hexp1, hexp2, hδ0]
          exact mul_le_mul_of_nonneg_right h5 (Nat.cast_nonneg _)
  · -- waste
    have hUU' : U \ rU' 𝓗 U ω = (Subtype.val '' (covX (res 𝓗 U) ω) : Set (Fin n)) := by
      ext x
      constructor
      · intro hx
        rw [rU'_sub] at hx
        by_contra hxc
        exact hx.2 ⟨hx.1, hxc⟩
      · intro hx
        refine ⟨?_, ?_⟩
        · obtain ⟨y, -, hyx⟩ := mem_image_iff' _ |>.mp hx
          rw [← hyx]; exact y.2
        · rw [rU'_sub]
          intro hc
          exact hc.2 hx
    have hsub : U \ (rU' 𝓗 U ω ∪ ⋃₀ rM 𝓗 U ω) ⊆
        (fun x : ↥U => (x : Fin n)) ''
          (covX (res 𝓗 U) ω \ ⋃ e ∈ isoFam (res 𝓗 U) ω, (e : Set ↥U)) := by
      intro x hx
      have hx1 : x ∈ U \ rU' 𝓗 U ω := ⟨hx.1, fun hc => hx.2 (Or.inl hc)⟩
      rw [hUU'] at hx1
      obtain ⟨y, hy, hyx⟩ := mem_image_iff' _ |>.mp hx1
      refine ⟨y, ⟨hy, ?_⟩, hyx⟩
      intro hyI
      obtain ⟨e, heIs, hey⟩ := mem_biUnion_iff'.mp hyI
      exact hx.2 (Or.inr ⟨(fun x : ↥U => (x : Fin n)) '' (e : Set ↥U),
        mem_rM.mpr ⟨e, heIs, rfl⟩, ⟨y, hey, hyx⟩⟩)
    calc ((U \ (rU' 𝓗 U ω ∪ ⋃₀ rM 𝓗 U ω)).ncard : ℝ)
        ≤ (((fun x : ↥U => (x : Fin n)) ''
            (covX (res 𝓗 U) ω \ ⋃ e ∈ isoFam (res 𝓗 U) ω, (e : Set ↥U))).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = ((covX (res 𝓗 U) ω \ ⋃ e ∈ isoFam (res 𝓗 U) ω, (e : Set ↥U)).ncard : ℝ) := by
          rw [ncard_valn]
      _ ≤ (r * collMult (res 𝓗 U) ω : ℕ) := by
          exact_mod_cast round_waste r (res 𝓗 U) ω (res_unif hu)
      _ = (r : ℝ) * (collMult (res 𝓗 U) ω : ℝ) := by push_cast; ring
      _ ≤ (r : ℝ) * ((1 + δ) * (θ - θ * Real.exp (-θ)) * (U.ncard : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg r)
          have h3 := hcl3
          rw [← hPg] at h3
          exact h3
      _ = r * (1 + δ) * (θ - θ * Real.exp (-θ)) * (U.ncard : ℝ) := by ring

end Work.Deep.Nibble
