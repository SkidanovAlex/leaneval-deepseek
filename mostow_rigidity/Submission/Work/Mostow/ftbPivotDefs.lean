import Mathlib
import Submission.Work.Mostow.ftbDefs
import Submission.Work.Mostow.nearIdAt_conj
import Submission.Work.Mostow.ftbPivotAux
import Submission.Work.Mostow.finiteFixesPoint
import Submission.Work.Mostow.notNearIdAtBlkOne

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-! ## Two elementary facts about `rotCanon` -/

/-- `rotCanon` is nonnegative (it is a rotation norm, or the junk value `0`). -/
private theorem rotCanon_nonnegD {N : ℕ} (hAall : ∀ k, Submission.Mostow.POActionProp k)
    (hIall : ∀ k, Submission.Mostow.HypIsometryProp k) (c : PO N 1) :
    0 ≤ rotCanon hAall hIall c := by
  rw [rotCanon]
  split
  · exact norm_nonneg _
  · exact le_refl 0

/-! ## The bound for the normal part of a block normal form

If `g` has a fixed point, is `η`-near the identity at `z` (`0 < η ≤ 1`), and
`h⁻¹ * g * h = e ▸ blk k m 1 R` is a block normal form with `R` fixed-point free, then
`rotN R ≤ C₀ * η`.  For `m ≥ 2` this is `nearId_rotN_bound` after transporting the
near-identity statement through the conjugation and the dimension cast; `m = 0` is trivial and
`m = 1` is impossible (a fixed-point-free isometry of `E 1` is `-1`, whose displacement is
bounded below by `arccosh (4 cosh 1 - 3) > 1 ≥ η`). -/
private theorem rotN_le_of_normalFormD {N : ℕ} (C₀ : ℝ) (hC₀pos : 0 < C₀)
    (hC₀ : ∀ (j m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (w : E (j + m)) (η : ℝ),
      POActionProp j → HypIsometryProp j → POActionProp (j + m) → HypIsometryProp (j + m) →
      2 ≤ m → 0 < η → η ≤ 1 → NearIdAt (blk j m 1 R) w η → rotN R ≤ C₀ * η)
    (hAall : ∀ k, POActionProp k) (hIall : ∀ k, HypIsometryProp k)
    (g : PO N 1) (z : E N) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hni : NearIdAt g z η)
    (k m : ℕ) (e : k + m = N) (h : PO N 1) (R : E m ≃ₗᵢ[ℝ] E m)
    (hRfree : ∀ w : E m, R w = w → w = 0)
    (hconj : h⁻¹ * g * h = (e ▸ blk k m 1 R : PO N 1)) :
    rotN R ≤ C₀ * η := by
  have hni' : NearIdAt (e ▸ blk k m 1 R : PO N 1) (h⁻¹ • z) η := by
    rw [← hconj]
    refine (nearIdAt_conj N (hAall N) (hIall N) h g (h⁻¹ • z) η).mpr ?_
    have hAb := POBasic.ofProp (hAall N)
    have hz : h • (h⁻¹ • z) = z := by
      rw [← hAb.mul_smul, mul_inv_cancel, hAb.one_smul]
    rwa [hz]
  have hcast : NearIdAt (blk k m 1 R) (e.symm ▸ (h⁻¹ • z) : E (k + m)) η :=
    nearIdAt_cast e (blk k m 1 R) (h⁻¹ • z) η hni'
  rcases m with _ | m
  · -- m = 0
    rw [rotN_e0 R]
    exact mul_nonneg hC₀pos.le hη0.le
  rcases m with _ | m
  · -- m = 1
    exact absurd hcast
      (notNearIdAtBlkOne k (hAall k) (hIall k) (hAall (k + 1)) (hIall (k + 1)) R hRfree
        (e.symm ▸ (h⁻¹ • z)) η hη1)
  · -- m = m + 2 ≥ 2
    exact hC₀ k (m + 2) R (e.symm ▸ (h⁻¹ • z)) η (hAall k) (hIall k)
      (e.symm ▸ hAall N) (e.symm ▸ hIall N) (by omega) hη0 hη1 hcast

/-! ## The pivot -/

/-- **The pivot and the rotation separation.**  Given a discrete `Λ ≤ PO N 1`, a point `z`,
`0 < η ≤ 1` and an elliptic `b₀ ∈ Λ ∖ {1}` that is `η`-near-identity at `z`, there is
`b ∈ Λ ∖ {1}` with a fixed point, with `rotCanon b ≤ C η` and the separation: every `c ∈ Λ` commuting with `b`
that fixes `Fix b` pointwise satisfies `rotCanon b ≤ C · rotCanon c`. -/
theorem ftbPivotDefs (N : ℕ) (hAall : ∀ k, Submission.Mostow.POActionProp k)
    (hIall : ∀ k, Submission.Mostow.HypIsometryProp k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : Subgroup (PO N 1)) (z : E N) (η : ℝ) (b₀ : PO N 1),
      IsDiscrete (SetLike.coe Λ) → b₀ ∈ Λ → b₀ ≠ 1 → 0 < η → η ≤ 1 →
      NearIdAt b₀ z η → (∃ p : E N, b₀ • p = p) →
      ∃ b : PO N 1, b ∈ Λ ∧ b ≠ 1 ∧ (∃ p : E N, b • p = p) ∧
        rotCanon hAall hIall b ≤ C * η ∧
        (∀ c : PO N 1, c ∈ Λ → c ∈ Subgroup.centralizer ({b} : Set (PO N 1)) →
          (∀ u : E N, b • u = u → c • u = u) → c ≠ 1 →
          rotCanon hAall hIall b ≤ C * rotCanon hAall hIall c) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := nearId_rotN_bound
  refine ⟨max 1 C₀, lt_of_lt_of_le zero_lt_one (le_max_left 1 C₀), ?_⟩
  intro Λ z η b₀ hdisc hb0 hb0ne hη0 hη1 hni hfix
  -- a point fixed by `b₀`
  set p : E N := hfix.choose with hp
  have hpfixed : b₀ • p = p := hfix.choose_spec
  -- the finite set of nontrivial elements of `Λ` fixing `Fix b₀` pointwise
  set P : Set (PO N 1) :=
    {c : PO N 1 | c ∈ Λ ∧ c ≠ 1 ∧ ∀ u : E N, b₀ • u = u → c • u = u} with hP
  have hmem : ∀ c : PO N 1,
      c ∈ P ↔ (c ∈ Λ ∧ c ≠ 1 ∧ ∀ u : E N, b₀ • u = u → c • u = u) := by
    intro c; simp only [hP, Set.mem_setOf_eq]
  have hPfin : P.Finite := by
    refine (finiteFixesPoint (hAall N) (hIall N) hdisc p).subset ?_
    intro c hc
    have hc' := (hmem c).mp hc
    exact ⟨hc'.1, hc'.2.2 p hpfixed⟩
  have hPne : P.Nonempty := ⟨b₀, (hmem b₀).mpr ⟨hb0, hb0ne, fun u hu => hu⟩⟩
  -- minimise `rotCanon` over `P`
  obtain ⟨b, hbP, hbmin⟩ :=
    Set.exists_min_image P (fun c : PO N 1 => rotCanon hAall hIall c) hPfin hPne
  have hb := (hmem b).mp hbP
  have hb0P : b₀ ∈ P := (hmem b₀).mpr ⟨hb0, hb0ne, fun u hu => hu⟩
  refine ⟨b, hb.1, hb.2.1, ⟨p, hb.2.2 p hpfixed⟩, ?_, ?_⟩
  · -- the size bound
    have h1 : rotCanon hAall hIall b ≤ rotCanon hAall hIall b₀ := hbmin b₀ hb0P
    have h2 : rotCanon hAall hIall b₀ ≤ C₀ * η := by
      rw [rotCanon, dif_pos hfix]
      let h_ef := elliptic_normal_form N (hAall N) (hIall N) hAall hIall b₀ hfix
      let k := h_ef.choose
      let m := h_ef.choose_spec.choose
      let e : k + m = N := h_ef.choose_spec.choose_spec.choose
      let hh : PO N 1 := h_ef.choose_spec.choose_spec.choose_spec.choose
      let R : E m ≃ₗᵢ[ℝ] E m := h_ef.choose_spec.choose_spec.choose_spec.choose_spec.choose
      have hRfree : ∀ w : E m, R w = w → w = 0 :=
        h_ef.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
      have hconj : hh⁻¹ * b₀ * hh = (e ▸ blk k m 1 R : PO N 1) :=
        h_ef.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2
      show rotN R ≤ C₀ * η
      exact rotN_le_of_normalFormD C₀ hC₀pos hC₀ hAall hIall b₀ z η hη0 hη1 hni
        k m e hh R hRfree hconj
    have h3 : C₀ * η ≤ max 1 C₀ * η := mul_le_mul_of_nonneg_right (le_max_right 1 C₀) hη0.le
    linarith
  · -- the separation
    intro c hcΛ _hcC hcfix hcne
    have hcP : c ∈ P := (hmem c).mpr ⟨hcΛ, hcne, fun u hu => hcfix u (hb.2.2 u hu)⟩
    have h1 : rotCanon hAall hIall b ≤ rotCanon hAall hIall c := hbmin c hcP
    have h2 : 0 ≤ rotCanon hAall hIall c := rotCanon_nonnegD hAall hIall c
    calc rotCanon hAall hIall b ≤ rotCanon hAall hIall c := h1
      _ ≤ max 1 C₀ * rotCanon hAall hIall c :=
          le_mul_of_one_le_left h2 (le_max_left 1 C₀)

end Work.Mostow
