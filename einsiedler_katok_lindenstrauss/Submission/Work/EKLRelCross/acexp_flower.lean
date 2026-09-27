import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.flower
import Submission.Work.EKLRelCross.pisa_crosssection
import Submission.Work.EKLRelCross.flower_plaque_bdd
import Submission.Work.EKLRelCross.freeSet_borel

open MeasureTheory Topology Filter
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

/-! ## 1. Elementary arithmetic of the displacement boxes `V` and the closed balls `Ucl` -/

/-- The identity lies in every closed ball. -/
private lemma one_mem_Ucl {U : Subgroup SL3} {a : ℝ} (ha : 0 ≤ a) :
    (1 : SL3) ∈ Ucl U a := by
  refine ⟨U.one_mem, fun i j => ?_⟩
  rw [show ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 from rfl, Matrix.one_apply]
  split_ifs <;> simp [ha]

/-- A closed ball is contained in the open ball of any strictly larger radius. -/
private lemma Ucl_subset_V {U : Subgroup SL3} {a b : ℝ} (h : a < b) : Ucl U a ⊆ V b :=
  fun _ hg i j => lt_of_le_of_lt (hg.2 i j) h

/-- An open ball is contained in the closed ball of the same radius. -/
private lemma V_subset_Ucl {U : Subgroup SL3} {a : ℝ} : V a ∩ (U : Set SL3) ⊆ Ucl U a :=
  fun _ hg => ⟨hg.2, fun i j => le_of_lt (hg.1 i j)⟩

/-- **Multiplicativity of the closed balls**: `Ucl a * Ucl b ⊆ Ucl (a + b + 3 a b)`. -/
private lemma mul_mem_Ucl {U : Subgroup SL3} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {x y : SL3}
    (hx : x ∈ Ucl U a) (hy : y ∈ Ucl U b) : x * y ∈ Ucl U (a + b + 3 * a * b) := by
  refine ⟨U.mul_mem hx.1 hy.1, fun i j => ?_⟩
  have hx' : ∀ k l, |(x : Matrix (Fin 3) (Fin 3) ℝ) k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ a :=
    fun k l => hx.2 k l
  have hy' : ∀ k l, |(y : Matrix (Fin 3) (Fin 3) ℝ) k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ b :=
    fun k l => hy.2 k l
  have hid : ((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1
      = ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)
        + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) + ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
  have hA : |((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ a := hx' i j
  have hB : |((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ b := hy' i j
  have hprod : |(((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j|
      ≤ 3 * (a * b) := by
    rw [Matrix.mul_apply]
    calc |∑ k : Fin 3, ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i k * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) k j|
        ≤ ∑ k : Fin 3, |((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i k
            * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 3, |((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i k|
            * |((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) k j| := by simp [abs_mul]
      _ ≤ ∑ _k : Fin 3, a * b :=
          Finset.sum_le_sum (fun k _ => mul_le_mul (hx' i k) (hy' k j) (abs_nonneg _) ha)
      _ = 3 * (a * b) := by simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hsum : |(((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j
        + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ 3 * (a * b) + a := by
    have h := abs_add_le ((((x : Matrix (Fin 3) (Fin 3) ℝ) - 1)
      * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j) (((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j)
    linarith
  have hmain : |(((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ 3 * (a * b) + a + b := by
    rw [hid, Matrix.add_apply, Matrix.add_apply]
    calc |((((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j
            + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j + ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j)|
        ≤ |(((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j
            + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j|
          + |((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| := abs_add_le _ _
      _ ≤ (3 * (a * b) + a) + b := add_le_add hsum hB
      _ = 3 * (a * b) + a + b := by ring
  rw [show ((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = (((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j from rfl]
  linarith

/-- A crude bound on the entries of the adjugate of an element of `V a` (i.e. of its inverse). -/
private lemma adjugate_entry_le {a : ℝ} (ha : 0 < a) {g : SL3} (hg : g ∈ V a) (i j : Fin 3) :
    |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j| ≤ 2 * (1 + a) ^ 2 :=
  Work.EKLProd.abs_adjugate_entry_le (by linarith)
    (fun p q => Work.EKLProd.mem_V_entries_le hg p q) i j

/-- The norm constant for the inverse of a `V a`-element. -/
private def Lam (a : ℝ) : ℝ := 2 * (1 + a) ^ 2 + 1

private lemma Lam_pos (a : ℝ) : 0 < Lam a := by
  have : (0:ℝ) ≤ 2 * (1 + a) ^ 2 := by positivity
  simp only [Lam]; linarith

/-- **The inverse of a small displacement is again a small displacement.** -/
private lemma inv_mem_Ucl {U : Subgroup SL3} {a : ℝ} (ha : 0 < a) {g : SL3} (hg : g ∈ V a)
    (hgU : g ∈ U) : g⁻¹ ∈ Ucl U (Lam a) := by
  refine ⟨U.inv_mem hgU, fun i j => ?_⟩
  have hcoe : ((g⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = (g : Matrix (Fin 3) (Fin 3) ℝ).adjugate :=
    Matrix.SpecialLinearGroup.coe_inv g
  rw [hcoe, Matrix.one_apply]
  have hb : |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j| ≤ 2 * (1 + a) ^ 2 :=
    adjugate_entry_le ha hg i j
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    calc |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i i - 1|
        ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i i| + |(1 : ℝ)| := abs_sub _ _
      _ = |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i i| + 1 := by rw [abs_one]
      _ ≤ 2 * (1 + a) ^ 2 + 1 := by linarith
      _ = Lam a := by simp only [Lam]
  · rw [if_neg hij]
    calc |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j - 0|
        = |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j| := by rw [sub_zero]
      _ ≤ 2 * (1 + a) ^ 2 := hb
      _ ≤ 2 * (1 + a) ^ 2 + 1 := by linarith
      _ = Lam a := by simp only [Lam]
/-! ## 2. The flower of a bounded cross-section -/

/-- The set of points whose `U`-orbit is free. -/
private def Free (U : Subgroup SL3) : Set X3 := {x | ∀ u ∈ U, u • x = x → u = 1}

private lemma mem_Free {U : Subgroup SL3} {x : X3} :
    x ∈ Free U ↔ ∀ u ∈ U, u • x = x → u = 1 := Iff.rfl

/-- `Free U` is invariant under the `U`-action. -/
private lemma mem_Free_smul {U : Subgroup SL3} {x : X3} (hx : x ∈ Free U) {u : SL3}
    (hu : u ∈ U) : u • x ∈ Free U := by
  intro w hw hwfix
  have h1 : (u⁻¹ * w * u) • x = x := by
    rw [mul_smul, mul_smul, hwfix, inv_smul_smul]
  have h2 : u⁻¹ * w * u = 1 := hx _ (U.mul_mem (U.mul_mem (U.inv_mem hu) hw) hu) h1
  calc w = u * (u⁻¹ * w * u) * u⁻¹ := by group
    _ = 1 := by rw [h2]; group


private lemma orbit_inj_of_mem_Free {U : Subgroup SL3} {x : X3} (hx : x ∈ Free U) :
    ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := by
  intro u₁ h₁ u₂ h₂ heq
  have hmem : u₂⁻¹ * u₁ ∈ U := U.mul_mem (U.inv_mem h₂) h₁
  have hfix : (u₂⁻¹ * u₁) • x = x := by rw [mul_smul, heq, inv_smul_smul]
  have h1 : u₂⁻¹ * u₁ = 1 := hx _ hmem hfix
  calc u₁ = u₂ * (u₂⁻¹ * u₁) := (mul_inv_cancel_left u₂ u₁).symm
    _ = u₂ * 1 := by rw [h1]
    _ = u₂ := mul_one u₂

/-- **The flower membership of a plaque point** (bounded form).  If `u ∈ V δ ∩ U` and `b ∈ B`,
then `u • b` lies in the flower set `flowerSet U δ B W` exactly when `b ∈ W`.  The cross-section
property is only needed for the bounded elements `w * u` (`w` ranging over the inverse of `V δ`),
which is why the hypothesis is stated with the closed ball `Ucl U Λ`. -/
private lemma flowerSet_mem_iff_of_mem_bdd {U : Subgroup SL3} {δ Λ : ℝ} {B W : Set X3}
    (hCS : ∀ x ∈ B, ∀ u ∈ U, u ∈ Ucl U Λ → u • x ∈ B → u = 1)
    (hδ : 0 < δ) (hΛ : Lam δ + δ + 3 * Lam δ * δ ≤ Λ)
    {u : SL3} (hu : u ∈ V δ ∩ (U : Set SL3)) {b' : X3} (hb' : b' ∈ B) :
    u • b' ∈ flowerSet U δ B W ↔ b' ∈ W := by
  constructor
  · rintro ⟨w, ⟨hw, hwU⟩, hwy⟩
    have hwUcl : w ∈ Ucl U (Lam δ) := by
      have h := inv_mem_Ucl hδ (g := w⁻¹) hw (U.inv_mem hwU)
      rwa [inv_inv] at h
    have huUcl : u ∈ Ucl U δ := ⟨hu.2, fun i j => le_of_lt (hu.1 i j)⟩
    have hwu : w * u ∈ Ucl U Λ :=
      Ucl_mono hΛ (mul_mem_Ucl (Lam_pos δ).le (le_of_lt hδ) hwUcl huUcl)
    have hmemB : (w * u) • b' ∈ B := by rw [mul_smul]; exact hwy.1
    have h1 : w * u = 1 := hCS b' hb' (w * u) (U.mul_mem hwU hu.2) hwu hmemB
    have : b' ∈ W := by
      have h2 : (w * u) • b' ∈ W := by rw [mul_smul]; exact hwy.2
      rwa [h1, one_smul] at h2
    exact this
  · intro hb'W
    refine ⟨u⁻¹, ⟨?_, U.inv_mem hu.2⟩, ?_⟩
    · show (u⁻¹)⁻¹ ∈ V δ
      rw [inv_inv]
      exact hu.1
    · show u⁻¹ • (u • b') ∈ B ∩ W
      have h : u⁻¹ • (u • b') = b' := by rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [h]
      exact ⟨hb', hb'W⟩

/-- **The atom of the flower σ-algebra at a plaque point is the plaque** (bounded form). -/
private theorem atom_flower_bdd {U : Subgroup SL3} {B : Set X3} {δ Λ : ℝ}
    (hCS : ∀ x ∈ B, ∀ u ∈ U, u ∈ Ucl U Λ → u • x ∈ B → u = 1)
    {W : ℕ → Set X3} (hW0 : W 0 = Set.univ)
    (hsep : ∀ b ∈ B, ∀ b' ∈ B, (∀ n, b ∈ W n ↔ b' ∈ W n) → b = b')
    (hδ : 0 < δ) (hΛ : Lam δ + δ + 3 * Lam δ * δ ≤ Λ)
    {v : SL3} (hv : v ∈ V δ) (hvU : v ∈ U) {b : X3} (hb : b ∈ B) :
    ∀ {x : X3}, x = v • b →
      atom (flowerSigma U δ B W) x
        = (fun u : SL3 => u • b) '' (V δ ∩ (U : Set SL3)) := by
  rintro x rfl
  have key : ∀ y : X3, y ∈ atom (flowerSigma U δ B W) (v • b)
      ↔ ∀ n, y ∈ flowerSet U δ B (W n) ↔ b ∈ W n := by
    intro y
    rw [show flowerSigma U δ B W
        = MeasurableSpace.generateFrom (Set.range (fun n => flowerSet U δ B (W n))) from rfl,
      mem_atom_iff_pattern]
    constructor
    · intro h n
      exact (h _ ⟨n, rfl⟩).trans (flowerSet_mem_iff_of_mem_bdd hCS hδ hΛ ⟨hv, hvU⟩ hb)
    · intro h A hA
      obtain ⟨n, rfl⟩ := hA
      exact (h n).trans (flowerSet_mem_iff_of_mem_bdd hCS hδ hΛ ⟨hv, hvU⟩ hb).symm
  ext y
  constructor
  · intro hy
    rw [key] at hy
    have hy0 : y ∈ flowerSet U δ B (W 0) := by rw [hy 0, hW0]; trivial
    obtain ⟨w, ⟨hw, hwU⟩, hwy⟩ := hy0
    set b' : X3 := w • y with hb'def
    have hb'B : b' ∈ B := by rw [hb'def]; exact hwy.1
    have hy_eq : y = w⁻¹ • b' := by rw [hb'def, ← mul_smul, inv_mul_cancel, one_smul]
    have hpat' : ∀ n, y ∈ flowerSet U δ B (W n) ↔ b' ∈ W n := by
      intro n
      rw [hy_eq]
      exact flowerSet_mem_iff_of_mem_bdd hCS hδ hΛ ⟨hw, U.inv_mem hwU⟩ hb'B
    have hb'b : b' = b := hsep b' hb'B b hb (fun n => (hpat' n).symm.trans (hy n))
    refine ⟨w⁻¹, ⟨hw, U.inv_mem hwU⟩, ?_⟩
    rw [← hb'b]
    exact hy_eq.symm
  · rintro ⟨u, ⟨hu, huU⟩, rfl⟩
    rw [key]
    intro n
    exact flowerSet_mem_iff_of_mem_bdd hCS hδ hΛ ⟨hu, huU⟩ hb

/-! ## 3. Almost every point has neighbourhoods of positive measure -/

private lemma ae_nhds_pos {μ : Measure X3} [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, 0 < μ s := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis X3
  have hsub : {x : X3 | ¬ (∀ s ∈ 𝓝 x, 0 < μ s)}
      ⊆ ⋃ (m : ℕ), (if μ (b m) = 0 then b m else ∅) := by
    intro x hx
    push Not at hx
    obtain ⟨s, hs, hszero⟩ := hx
    obtain ⟨t, ht, hxt, hts⟩ := hb.mem_nhds_iff.mp hs
    obtain ⟨m, rfl⟩ := ht
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    have hzero : μ (b m) = 0 := le_antisymm (le_trans (measure_mono hts) hszero) bot_le
    rw [if_pos hzero]
    exact hxt
  have hnull : μ (⋃ (m : ℕ), (if μ (b m) = 0 then b m else ∅)) = 0 := by
    refine measure_iUnion_null (fun m => ?_)
    by_cases hm : μ (b m) = 0
    · rw [if_pos hm]; exact hm
    · rw [if_neg hm]; exact measure_empty
  rw [MeasureTheory.ae_iff]
  exact measure_mono_null hsub hnull

/-! ## 4. Countably many bounded cross-sections covering almost everything -/

private lemma exists_countable_crosssections {μ : Measure X3} [IsProbabilityMeasure μ]
    {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3)) {ρ : ℝ} (hρ : 2 < ρ)
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) :
    ∃ (E C : ℕ → Set X3),
      (∀ n, IsClosed (E n) ∧ C n ⊆ E n ∧ MeasurableSet (C n) ∧
        (∀ x ∈ E n, ∃! t : SL3, t ∈ Ucl U 1 ∧ t • x ∈ C n) ∧
        (∀ c ∈ C n, ∀ u ∈ Ucl U ρ, u • c ∈ C n → u = 1)) ∧
      (∀ n, 0 < μ (E n)) ∧ μ (⋃ n, E n)ᶜ = 0 := by
  classical
  set F : Set X3 := Free U with hFdef
  set D : Set X3 := {x : X3 | ∀ s ∈ 𝓝 x, 0 < μ s} with hDdef
  have hFfree : ∀ x ∈ F, ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ :=
    fun x hx => orbit_inj_of_mem_Free hx
  have hFae : ∀ᵐ x ∂μ, x ∈ F := hfree
  have hDae : ∀ᵐ x ∂μ, x ∈ D := ae_nhds_pos
  have hFDcompl : μ (F ∩ D)ᶜ = 0 := by
    have h1 : (F ∩ D)ᶜ ⊆ Fᶜ ∪ Dᶜ := by
      intro x hx
      rcases Classical.em (x ∈ F) with hF | hF
      · refine Or.inr ?_
        intro hD
        exact hx ⟨hF, hD⟩
      · exact Or.inl hF
    refine measure_mono_null h1 (measure_union_null ?_ ?_)
    · rw [MeasureTheory.ae_iff] at hFae; exact hFae
    · rw [MeasureTheory.ae_iff] at hDae; exact hDae
  have hFDne : (F ∩ D).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    have : μ (Set.univ : Set X3) = 0 := by
      have huniv : (Set.univ : Set X3) = (F ∩ D)ᶜ := by rw [hemp, Set.compl_empty]
      rw [huniv]; exact hFDcompl
    rw [measure_univ] at this
    exact one_ne_zero this
  obtain ⟨x₀, hx₀⟩ := hFDne
  obtain ⟨hx₀F, hx₀D⟩ := hx₀
  -- the pair produced by the cross-section construction at a free point
  have hpick : ∀ x : X3, x ∈ F → ∃ p : Set X3 × Set X3,
      IsClosed p.1 ∧ x ∈ interior p.1 ∧ p.2 ⊆ p.1 ∧ MeasurableSet p.2 ∧
      (∀ y ∈ p.1, ∃! t : SL3, t ∈ Ucl U 1 ∧ t • y ∈ p.2) ∧
      (∀ c ∈ p.2, ∀ u ∈ Ucl U ρ, u • c ∈ p.2 → u = 1) := by
    intro x hx
    obtain ⟨E, C, h1, h2, h3, h4, h5, h6⟩ := pisa_crosssection hUcl x hρ (hFfree x hx)
    exact ⟨(E, C), h1, h2, h3, h4, h5, h6⟩
  let P : X3 → Set X3 × Set X3 := fun x =>
    if hx : x ∈ F then Classical.choose (hpick x hx) else (Set.univ, Set.univ)
  have hPprop : ∀ x (hx : x ∈ F), IsClosed (P x).1 ∧ x ∈ interior (P x).1 ∧ (P x).2 ⊆ (P x).1 ∧
      MeasurableSet (P x).2 ∧
      (∀ y ∈ (P x).1, ∃! t : SL3, t ∈ Ucl U 1 ∧ t • y ∈ (P x).2) ∧
      (∀ c ∈ (P x).2, ∀ u ∈ Ucl U ρ, u • c ∈ (P x).2 → u = 1) := by
    intro x hx
    have hPx : P x = Classical.choose (hpick x hx) := by simp only [P, dif_pos hx]
    rw [hPx]
    exact Classical.choose_spec (hpick x hx)
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis X3
  -- for each basis element, a centre inside it (when a good centre exists)
  let Good : ℕ → Prop := fun n => ∃ y : X3, y ∈ F ∧ y ∈ D ∧ y ∈ b n ∧ b n ⊆ interior (P y).1
  let ctr : ℕ → X3 := fun n => if h : Good n then Classical.choose h else x₀
  have hctrF : ∀ n, ctr n ∈ F := by
    intro n
    by_cases h : Good n
    · simp only [ctr, dif_pos h]
      exact (Classical.choose_spec h).1
    · simp only [ctr, dif_neg h]
      exact hx₀F
  have hctrD : ∀ n, ∀ s ∈ 𝓝 (ctr n), 0 < μ s := by
    intro n
    by_cases h : Good n
    · simp only [ctr, dif_pos h]
      exact (Classical.choose_spec h).2.1
    · simp only [ctr, dif_neg h]
      exact hx₀D
  have hctrmem : ∀ n, Good n → ctr n ∈ b n := by
    intro n h
    simp only [ctr, dif_pos h]
    exact (Classical.choose_spec h).2.2.1
  have hctrsub : ∀ n, Good n → b n ⊆ interior (P (ctr n)).1 := by
    intro n h
    simp only [ctr, dif_pos h]
    exact (Classical.choose_spec h).2.2.2
  -- the basis covers the good set
  have hcover : F ∩ D ⊆ ⋃ n, (P (ctr n)).1 := by
    intro y hy
    obtain ⟨hyF, hyD⟩ := hy
    have hmem : interior (P y).1 ∈ 𝓝 y := isOpen_interior.mem_nhds ((hPprop y hyF).2.1)
    obtain ⟨t, ht, hyt, hts⟩ := hb.mem_nhds_iff.mp hmem
    obtain ⟨n, rfl⟩ := ht
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    exact interior_subset (hctrsub n ⟨y, hyF, hyD, hyt, hts⟩ hyt)
  have hEpos : ∀ n, 0 < μ ((P (ctr n)).1) := by
    intro n
    by_cases h : Good n
    · have hbnhds : b n ∈ 𝓝 (ctr n) := (hb.isOpen ⟨n, rfl⟩).mem_nhds (hctrmem n h)
      have hpos : 0 < μ (b n) := hctrD n (b n) hbnhds
      exact lt_of_lt_of_le hpos (measure_mono (fun x hx => interior_subset (hctrsub n h hx)))
    · have hctrx : ctr n = x₀ := by simp only [ctr, dif_neg h]
      have hmem : interior (P x₀).1 ∈ 𝓝 x₀ := isOpen_interior.mem_nhds ((hPprop x₀ hx₀F).2.1)
      have hpos : 0 < μ ((P x₀).1) :=
        lt_of_lt_of_le (hx₀D _ hmem) (measure_mono interior_subset)
      rwa [hctrx]
  refine ⟨fun n => (P (ctr n)).1, fun n => (P (ctr n)).2, ?_, hEpos, ?_⟩
  · intro n
    obtain ⟨h1, _h2, h3, h4, h5, h6⟩ := hPprop (ctr n) (hctrF n)
    exact ⟨h1, h3, h4, h5, h6⟩
  · have hsub : (⋃ n, (P (ctr n)).1)ᶜ ⊆ (F ∩ D)ᶜ := by
      intro x hx hcon
      exact hx (hcover hcon)
    exact measure_mono_null hsub hFDcompl


theorem acexp_flower {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U) {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) :
    ∀ R : ℝ, 0 < R → ∃ (K : ℕ → Set Work.EKLContract.X3) (m : ℕ → MeasurableSpace Work.EKLContract.X3),
      (∀ k, Work.EKLContract.IsPlaqueAlgebra U (K k) (m k)) ∧
      (∀ k, 0 < μ (K k)) ∧
      ∀ᵐ y ∂μ, ∃ k, y ∈ K k ∧
        (fun u : Work.EKLContract.SL3 => u • y) '' (Work.EKLContract.V R ∩ (U : Set Work.EKLContract.SL3)) ⊆ Work.EKLContract.atom (m k) y := by
  intro R hR
  have hUcl : IsClosed (U : Set SL3) := hU.1
  have hR0 : 0 ≤ R := le_of_lt hR
  set δ : ℝ := 100 * (R + 1) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  set ρ : ℝ := 2 * (1 + δ) ^ 2 + 1 + δ + 3 * (2 * (1 + δ) ^ 2 + 1) * δ + 10 with hρdef
  have hΛ : 2 * (1 + δ) ^ 2 + 1 + δ + 3 * (2 * (1 + δ) ^ 2 + 1) * δ ≤ ρ := by
    rw [hρdef]; linarith
  have hρ2 : 2 < ρ := by
    have h1 : (0 : ℝ) < δ + 10 := by linarith
    have h2 : (0 : ℝ) ≤ 2 * (1 + δ) ^ 2 + 1 + 3 * (2 * (1 + δ) ^ 2 + 1) * δ := by positivity
    rw [hρdef]; linarith
  have hLam2eq : Lam 2 = 19 := by norm_num [Lam]
  have hLam2lt : Lam 2 < δ := by rw [hLam2eq, hδdef]; linarith
  have hMulLt : R + Lam 2 + 3 * R * Lam 2 < δ := by rw [hLam2eq, hδdef]; linarith
  obtain ⟨E, C, hEC, hEpos, hEcover⟩ :=
    exists_countable_crosssections hUcl hρ2 hfree
  obtain ⟨bs, hbs⟩ := TopologicalSpace.exists_seq_basis X3
  set W : ℕ → Set X3 := fun n => if n = 0 then Set.univ else bs (n - 1) with hWdef
  have hW0 : W 0 = Set.univ := by simp [hWdef]
  have hWopen : ∀ n, IsOpen (W n) := by
    intro n
    by_cases hn : n = 0
    · rw [hWdef]; simp [hn]
    · rw [hWdef]; simp only [hn, if_false]
      exact hbs.isOpen (Set.mem_range_self (n - 1))
  have hWmeas : ∀ n, MeasurableSet (W n) := fun n => (hWopen n).measurableSet
  have hWgen : borel X3 = MeasurableSpace.generateFrom (Set.range W) := by
    refine le_antisymm ?_ ?_
    · rw [hbs.borel_eq_generateFrom]
      refine MeasurableSpace.generateFrom_mono ?_
      rintro t ⟨m, rfl⟩
      exact ⟨m + 1, by rw [hWdef]; simp⟩
    · refine MeasurableSpace.generateFrom_le (fun t ht => ?_)
      obtain ⟨n, rfl⟩ := ht
      exact (hWopen n).measurableSet
  have hWsepAll : ∀ x y : X3, (∀ n, x ∈ W n ↔ y ∈ W n) → x = y := by
    intro x y hpat
    by_contra hne
    obtain ⟨a₁, a₂, ha₁, ha₂, hxa₁, hya₂, hdisj⟩ := t2_separation hne
    obtain ⟨t₀, ht₀, hxt₀, ht₀a₁⟩ := (hbs.isOpen_iff.mp ha₁) x hxa₁
    obtain ⟨m, rfl⟩ := ht₀
    have h1 : x ∈ W (m + 1) := by
      rw [hWdef]; simp only [Nat.succ_ne_zero, if_false]; simpa using hxt₀
    have h2 : y ∉ W (m + 1) := by
      rw [hWdef]; simp only [Nat.succ_ne_zero, if_false]
      intro hmem
      exact (Set.disjoint_left.mp hdisj (ht₀a₁ hmem)) hya₂
    exact h2 ((hpat (m + 1)).mp h1)
  have hfreeNull : μ ((Free U)ᶜ) = 0 := by
    have h := MeasureTheory.ae_iff.mp hfree
    rw [show (Free U)ᶜ = {x : X3 | ¬ ∀ u ∈ U, u • x = x → u = 1} from rfl]
    exact h
  refine ⟨fun k => ⋃ c ∈ (C k ∩ Free U), atom (flowerSigma U δ (C k) W) c,
    fun k => flowerSigma U δ (C k) W, ?_, ?_, ?_⟩
  · intro k
    exact flower_plaque_bdd hUcl hδpos hΛ
      (fun c hc u _ hu huc => (hEC k).2.2.2.2 c hc u hu huc)
      (hEC k).2.2.1 hW0 hWmeas hWgen
      (fun x _ y _ h => hWsepAll x y h) (freeSet_borel hUcl)
  · intro k
    have hCSk : ∀ c ∈ C k, ∀ u ∈ U, u ∈ Ucl U ρ → u • c ∈ C k → u = 1 :=
      fun c hc u _ hu huc => (hEC k).2.2.2.2 c hc u hu huc
    have hsep : ∀ b ∈ C k, ∀ b' ∈ C k, (∀ n, b ∈ W n ↔ b' ∈ W n) → b = b' :=
      fun b _ b' _ h => hWsepAll b b' h
    have hsub : E k ∩ Free U ⊆ ⋃ c ∈ (C k ∩ Free U), atom (flowerSigma U δ (C k) W) c := by
      intro y ⟨hyE, hyF⟩
      obtain ⟨t, ⟨htUcl, htyC⟩, -⟩ := (hEC k).2.2.2.1 y hyE
      have htU : t ∈ U := htUcl.1
      have htV2 : t ∈ V 2 := Ucl_subset_V (by norm_num) htUcl
      have htinvUcl : t⁻¹ ∈ Ucl U (Lam 2) := inv_mem_Ucl (by norm_num) htV2 htU
      have htinvV : t⁻¹ ∈ V δ := Ucl_subset_V hLam2lt htinvUcl
      have hcF : t • y ∈ Free U := mem_Free_smul hyF htU
      refine Set.mem_iUnion.mpr ⟨t • y, Set.mem_iUnion.mpr ⟨⟨htyC, hcF⟩, ?_⟩⟩
      have hatom : atom (flowerSigma U δ (C k) W) (t • y)
          = (fun w : SL3 => w • (t • y)) '' (V δ ∩ (U : Set SL3)) :=
        atom_flower_bdd hCSk hW0 hsep hδpos hΛ (v := (1 : SL3))
          (Work.EKLContract.Lemmas.V_open_one δ hδpos).2 U.one_mem htyC (x := t • y)
          (by rw [one_smul])
      rw [hatom]
      refine ⟨t⁻¹, ⟨htinvV, U.inv_mem htU⟩, ?_⟩
      show t⁻¹ • (t • y) = y
      rw [inv_smul_smul]
    have h2 : μ (E k) ≤ μ (E k ∩ Free U) := by
      have hs : E k ⊆ (E k ∩ Free U) ∪ (Free U)ᶜ := by
        intro z hz
        by_cases h : z ∈ Free U
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr h
      calc μ (E k) ≤ μ ((E k ∩ Free U) ∪ (Free U)ᶜ) := measure_mono hs
        _ ≤ μ (E k ∩ Free U) + μ ((Free U)ᶜ) := measure_union_le _ _
        _ = μ (E k ∩ Free U) := by rw [hfreeNull, add_zero]
    exact lt_of_lt_of_le (hEpos k) (le_trans h2 (measure_mono hsub))
  · have hEae : ∀ᵐ y ∂μ, y ∈ ⋃ n, E n := by
      have h : μ {y : X3 | ¬ y ∈ ⋃ n, E n} = 0 := by
        simpa only [Set.compl_def] using hEcover
      exact MeasureTheory.ae_iff.mpr h
    filter_upwards [hfree, hEae] with y hyF hycov
    obtain ⟨k, hyE⟩ := Set.mem_iUnion.mp hycov
    have hCSk : ∀ c ∈ C k, ∀ u ∈ U, u ∈ Ucl U ρ → u • c ∈ C k → u = 1 :=
      fun c hc u _ hu huc => (hEC k).2.2.2.2 c hc u hu huc
    have hsep : ∀ b ∈ C k, ∀ b' ∈ C k, (∀ n, b ∈ W n ↔ b' ∈ W n) → b = b' :=
      fun b _ b' _ h => hWsepAll b b' h
    obtain ⟨t, ⟨htUcl, htyC⟩, -⟩ := (hEC k).2.2.2.1 y hyE
    have htU : t ∈ U := htUcl.1
    have htV2 : t ∈ V 2 := Ucl_subset_V (by norm_num) htUcl
    have htinvUcl : t⁻¹ ∈ Ucl U (Lam 2) := inv_mem_Ucl (by norm_num) htV2 htU
    have htinvV : t⁻¹ ∈ V δ := Ucl_subset_V hLam2lt htinvUcl
    have hcF : t • y ∈ Free U := mem_Free_smul hyF htU
    refine ⟨k, ?_, ?_⟩
    · refine Set.mem_iUnion.mpr ⟨t • y, Set.mem_iUnion.mpr ⟨⟨htyC, hcF⟩, ?_⟩⟩
      have hatom : atom (flowerSigma U δ (C k) W) (t • y)
          = (fun w : SL3 => w • (t • y)) '' (V δ ∩ (U : Set SL3)) :=
        atom_flower_bdd hCSk hW0 hsep hδpos hΛ (v := (1 : SL3))
          (Work.EKLContract.Lemmas.V_open_one δ hδpos).2 U.one_mem htyC (x := t • y)
          (by rw [one_smul])
      rw [hatom]
      refine ⟨t⁻¹, ⟨htinvV, U.inv_mem htU⟩, ?_⟩
      show t⁻¹ • (t • y) = y
      rw [inv_smul_smul]
    · have hatomy : atom (flowerSigma U δ (C k) W) y
          = (fun w : SL3 => w • (t • y)) '' (V δ ∩ (U : Set SL3)) :=
        atom_flower_bdd hCSk hW0 hsep hδpos hΛ (v := t⁻¹) htinvV (U.inv_mem htU) htyC
          (x := y) (by rw [inv_smul_smul])
      rintro z ⟨u, hu, rfl⟩
      obtain ⟨huVR, huU⟩ := hu
      rw [hatomy]
      refine ⟨u * t⁻¹, ⟨?_, U.mul_mem huU (U.inv_mem htU)⟩, ?_⟩
      · exact Ucl_subset_V hMulLt (mul_mem_Ucl hR0 (Lam_pos 2).le
          (V_subset_Ucl ⟨huVR, huU⟩) htinvUcl)
      · show (u * t⁻¹) • (t • y) = u • y
        rw [mul_smul, inv_smul_smul]


end Work.EKLRelCross
