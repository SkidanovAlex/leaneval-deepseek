import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.EKLComp.exists_bump
import Submission.Work.EKLComp.exists_level_null
import Submission.Work.EKLComp.exists_bump_on_ball
import Submission.Work.EKLComp.exists_finPart_level
import Submission.Work.EKLNonExc.VFacts

namespace Work.EKLComp

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

set_option linter.unusedVariables false

theorem exists_small_part (K : Set Work.EKLContract.X3) (hK : IsCompact K) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ) : ∃ P : Work.EKLContract.FinPart Work.EKLContract.X3, (∀ i (x : Work.EKLContract.X3), x ∈ K → x ∈ P.parts i → ∀ y ∈ K, y ∈ P.parts i → y ∈ Work.EKLComp.ball δ x) ∧ (∀ i, μ (frontier (P.parts i)) = 0) := by
  by_cases hKe : K = ∅
  · -- `K` empty: the one-part partition on `univ` has empty frontier.
    refine ⟨⟨1, fun _ => Set.univ, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact fun _ => MeasurableSet.univ
    · exact fun i j hij => absurd (Subsingleton.elim i j) hij
    · ext x; simp
    · intro i x hx hxi y hy hyi
      exact (Set.eq_empty_iff_forall_notMem.mp hKe y hy).elim
    · intro i
      rw [frontier_univ]
      exact measure_empty
  · -- `K` nonempty.
    -- Choose a common scale at which two `ε`-close displacements of a point compose.
    obtain ⟨ε, hεpos, hεmul⟩ := Work.EKLNonExc.V_mul_inv (δ := δ) hδ
    set R : ℝ := ε / 4 with hRdef
    have hRpos : 0 < R := by rw [hRdef]; linarith
    have h2Rε : 2 * R ≤ ε := by rw [hRdef]; linarith
    have hR2R : R < 2 * R := by linarith
    -- A finite cover of `K` by `R`-balls.
    have hcover : K ⊆ ⋃ y : Work.EKLContract.X3, ball R y :=
      fun x _ => Set.mem_iUnion.mpr ⟨x, self_mem_ball hRpos x⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : Work.EKLContract.X3 => ball R y)
      (fun y => isOpen_ball R y) hcover
    have htne : t.Nonempty := by
      rcases Finset.eq_empty_or_nonempty t with h | h
      · exfalso
        apply hKe
        refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
        have hx' := ht hx
        rw [h] at hx'
        simpa using hx'
      · exact h
    let ι := {y : Work.EKLContract.X3 // y ∈ t}
    haveI : Fintype ι := inferInstance
    have hιne : Nonempty ι := by
      obtain ⟨y, hy⟩ := htne
      exact ⟨⟨y, hy⟩⟩
    have hmne : (Fintype.card ι : ℝ) ≠ 0 := by
      have h : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hιne
      exact_mod_cast h.ne'
    -- Bumps: `ψ i = 1` on `ball R yᵢ` and `ψ i = 0` off `ball (2R) yᵢ`.
    have hbump : ∀ i : ι, ∃ ψ : Work.EKLContract.X3 → ℝ, Continuous ψ ∧
        (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧ (∀ x ∈ ball R i.val, ψ x = 1) ∧
        (∀ x, x ∉ ball (2 * R) i.val → ψ x = 0) :=
      fun i => exists_bump_on_ball i.val hRpos hR2R
    choose ψ hψcont hψrange hψ1 hψ0 using hbump
    let σ : Work.EKLContract.X3 → ℝ := fun x => ∑ i : ι, ψ i x
    let ρ : Work.EKLContract.X3 → ℝ := fun x => max (σ x) (1 / 2)
    let Φ : ι → Work.EKLContract.X3 → ℝ := fun i x => ψ i x / ρ x
    have hσcont : Continuous σ := by
      simp only [σ]
      exact continuous_finsetSum _ (fun i _ => hψcont i)
    have hρcont : Continuous ρ := hσcont.max continuous_const
    have hρpos : ∀ x, 0 < ρ x := fun x =>
      lt_of_lt_of_le (by norm_num) (le_max_right (σ x) (1 / 2))
    have hΦcont : ∀ i, Continuous (Φ i) := fun i =>
      (hψcont i).div hρcont (fun x => (hρpos x).ne')
    -- On `K` some bump equals `1`, hence the `Φ i` form a partition of unity there.
    have hcoverK : ∀ x ∈ K, ∃ i : ι, ψ i x = 1 := by
      intro x hx
      have hx' := ht hx
      rw [Set.mem_iUnion] at hx'
      obtain ⟨y, hy⟩ := hx'
      rw [Set.mem_iUnion] at hy
      obtain ⟨hyt, hxy⟩ := hy
      exact ⟨⟨y, hyt⟩, hψ1 ⟨y, hyt⟩ x hxy⟩
    have hσK : ∀ x ∈ K, 1 ≤ σ x := by
      intro x hx
      obtain ⟨i, hi⟩ := hcoverK x hx
      have hle : ψ i x ≤ ∑ j : ι, ψ j x :=
        Finset.single_le_sum (f := fun j : ι => ψ j x) (fun j _ => (hψrange j x).1)
          (Finset.mem_univ i)
      show 1 ≤ ∑ j : ι, ψ j x
      rw [← hi]
      exact hle
    have hΦsum : ∀ x ∈ K, ∑ i : ι, Φ i x = 1 := by
      intro x hx
      have hσ1 : 1 ≤ σ x := hσK x hx
      have hρeq : ρ x = σ x := max_eq_left (le_trans (by norm_num) hσ1)
      have hσx : (∑ i : ι, ψ i x) = σ x := rfl
      show (∑ i : ι, ψ i x / ρ x) = 1
      rw [← Finset.sum_div, hσx, hρeq, div_self (by linarith : σ x ≠ 0)]
    -- A level at which all the `Φ i` have null fibres.
    obtain ⟨c, hcpos, hclt1, hclevel⟩ := exists_level_null μ
      (fun k : Fin (Fintype.card ι) =>
        fun x => (Fintype.card ι : ℝ) * Φ ((Fintype.equivFin ι).symm k) x)
      (fun k => (continuous_const.mul (hΦcont ((Fintype.equivFin ι).symm k))).measurable)
    set c₀ : ℝ := c / (Fintype.card ι) with hc₀def
    have hc₀pos : 0 < c₀ := by
      rw [hc₀def]
      exact div_pos hcpos (by exact_mod_cast (Fintype.card_pos_iff.mpr hιne))
    have hc₀lt : (Fintype.card ι : ℝ) * c₀ < 1 := by
      rw [hc₀def, mul_div_cancel₀ c hmne]
      exact hclt1
    have hc₀null : ∀ i : ι, μ (Φ i ⁻¹' ({c₀} : Set ℝ)) = 0 := by
      intro i
      have hk := hclevel (Fintype.equivFin ι i)
      rw [Equiv.symm_apply_apply] at hk
      have hset : (fun x => (Fintype.card ι : ℝ) * Φ i x) ⁻¹' ({c} : Set ℝ)
          = Φ i ⁻¹' ({c₀} : Set ℝ) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hc₀def]
        rw [eq_div_iff hmne]
        constructor <;> intro h <;> linarith
      rw [hset] at hk
      exact hk
    -- The partition associated with the level sets.
    obtain ⟨P, hPbound, hPcases⟩ := exists_finPart_level μ Φ hΦcont (c := c₀) hc₀null
    refine ⟨P, ?_, hPbound⟩
    intro i x hxK hxP y hyK hyP
    have hex : ∃ i₀ : ι, c₀ < Φ i₀ x := by
      by_contra h
      push_neg at h
      have h1 : (∑ j : ι, Φ j x) ≤ ∑ _j : ι, c₀ := Finset.sum_le_sum (fun j _ => h j)
      rw [hΦsum x hxK] at h1
      have h2 : (∑ _j : ι, c₀) = (Fintype.card ι : ℝ) * c₀ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [h2] at h1
      linarith [hc₀lt]
    obtain ⟨i₀, hi₀⟩ := hex
    rcases hPcases i with ⟨i₁, hi₁⟩ | hbelow
    · -- `x, y` lie in the same `2R`-ball around `yᵢ₁`
      have hxU : x ∈ ball (2 * R) i₁.val := by
        by_contra hxc
        have h0 : Φ i₁ x = 0 := by
          have h := hψ0 i₁ x hxc
          simp [Φ, h]
        have hgt : c₀ < Φ i₁ x := hi₁ hxP
        rw [h0] at hgt
        exact absurd hgt (not_lt.mpr hc₀pos.le)
      have hyU : y ∈ ball (2 * R) i₁.val := by
        by_contra hyc
        have h0 : Φ i₁ y = 0 := by
          have h := hψ0 i₁ y hyc
          simp [Φ, h]
        have h1 : 0 < Φ i₁ y := lt_trans hc₀pos (hi₁ hyP)
        rw [h0] at h1
        exact lt_irrefl 0 h1
      obtain ⟨g, hgV, hgx⟩ := hxU
      obtain ⟨h, hhV, hhy⟩ := hyU
      have hgε : g ∈ Work.EKLContract.V ε := V_mono h2Rε hgV
      have hhε : h ∈ Work.EKLContract.V ε := V_mono h2Rε hhV
      refine ⟨h * g⁻¹, hεmul g hgε h hhε, ?_⟩
      show (h * g⁻¹) • x = y
      rw [mul_smul, ← hgx, inv_smul_smul]
      exact hhy
    · exact absurd (hbelow hxP i₀) (not_le.mpr hi₀)

end

end Work.EKLComp
