import Mathlib
import Submission.Work.EKLC6Core.CellWDefs
import Submission.Work.EKLC6Core.cell_relthin_cover2
import Submission.Work.EKLC6Core.cell_relative_depth
import Submission.Work.EKLC6Core.cell_relative_depth_fixed
import Submission.Work.EKLC6Core.ae_injCap_depth
import Submission.Work.EKLC6Core.cell_facts_of_base
import Submission.Work.EKLC6Core.cellW_atom_shape
import Submission.Work.EKLC6Core.cellW_margin
import Submission.Work.EKLC6Core.margin_mem_atom_pointwise
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLComp.LeafDefs

/-!
# `Work.EKLC6Core.cellW_margin_exists_sep` — a cell system whose shapes contain the
contracting balls along the orbit, with a separating family of cylinders

For an `aDiag t`-invariant probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` with `Uminus t ≠ ⊥` there
are

* a cell system `S : CellW μ (Uminus t)` (the *relative* cover of
  `Work.EKLC6Core.cellW_relthin_cover`, whose collar of relative width `ε` has mass `≤ C ε ^ α`),
* a countable family `O` of open sets of `SL₃(ℝ)` separating the left `Uminus t`-cosets
  (`Work.EKLC6Core.exists_base_sat_sep`),
* rates `0 < lam < mu < 1` with `lam ≥ exp (t i - t j)` for all `i < j` with `t i < t j`

such that along the orbit of a.e. `x`, whenever the orbit point `yₙ` lies in a cell `S.Q k`, the
whole `Uminus t`-ball of radius `mu ^ n` around `yₙ` lies in the shape of the `MSigW S O`-atom at
`yₙ`.

## Proof

`mu` is chosen *below* `1` but *above* the contraction rate
`lam := max {exp (t i - t j) | t i < t j}` of `aDiag t` on `Uminus t`; this is why the rate `mu`
of the conclusion is available although the cell family is the *relative* one.

The two a.e. inputs along the orbit are

* **relative depth** (`Work.EKLC6Core.cell_relative_depth_of_disjoint`): the orbit point is
  `γ ^ n`-deep inside whichever cell contains it *relative to its own injectivity radius*, for
  every `γ ∈ (0,1)`;
* **subexponential decay of the injectivity radius** (`Work.EKLC6Core.ae_injCap_depth`): for every
  `δ > 0`, eventually `injCap (yₙ) ≥ e^{-δ n}`.

Their product gives `mu ^ n` where `mu := γ * e^{-δ}`, and `γ` (close to `1`) and `δ` (small) are
chosen so that `mu` lies in `(lam, 1)`.  The `Uminus t`-membership in the atom is then
`Work.EKLC6Core.margin_mem_atom_pointwise` (`U`-invariance of the saturated cylinders plus the
local `U`-equivariance of the canonical lift, which needs the depth at scale
`c ^ n` only through `margin_le_cellDeltaW`).
-/

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

theorem cellW_margin_exists_sep {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hne : Work.EKLC6Core.Uminus t ≠ ⊥) :
    ∃ (S : Work.EKLC6Core.CellW μ (Work.EKLC6Core.Uminus t)) (O : ℕ → Set Work.EKLContract.SL3)
      (lam mu : ℝ),
      0 < lam ∧ lam < mu ∧ mu < 1 ∧
      (∀ i j : Fin 3, t i < t j → Real.exp (t i - t j) ≤ lam) ∧
      (∀ m, IsOpen (O m)) ∧
      (∀ g g' : Work.EKLContract.SL3,
        (∀ m, (∃ u ∈ Work.EKLC6Core.Uminus t, u * g ∈ O m) ↔
          (∃ u ∈ Work.EKLC6Core.Uminus t, u * g' ∈ O m)) →
        ∃ u ∈ Work.EKLC6Core.Uminus t, g' = u * g) ∧
      (∀ k m, MeasurableSet (Work.EKLC6Core.genCW S O k m)) ∧
      ∃ ε : Work.EKLContract.X3 → ℝ, ∀ᵐ x ∂μ, 0 < ε x ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ,
        ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x ∈ S.Q k →
        Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) (ε x * mu ^ n) ⊆
          Work.EKLContract.shape (Work.EKLC6Core.MSigW S O) (Work.EKLC6Core.Uminus t)
            (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) := by
  classical
  -- ## 1. The relative cover, with its relative thinness
  obtain ⟨Q, δ, g, C, α, hopen, hdisj, hcover, hδ, hsub, hinj, hC, hα, hthin⟩ :=
    cell_relthin_cover2 (μ := μ)
  let S : Work.EKLC6Core.CellW μ (Work.EKLC6Core.Uminus t) :=
    { Q := Q, hopen := hopen, hdisj := hdisj, hcover := hcover, δ := δ,
      hδpos := fun k => (hδ k).1, hδsmall := fun k => (hδ k).2, g := g, hsub := hsub,
      hinj := hinj }
  -- ## 2. The separating family of open cylinders
  obtain ⟨O, hOopen, -, hOsep_sat⟩ :=
    exists_base_sat_sep (Work.EKLC6Core.Uminus t) (Work.EKLC6Core.uminus_isHoro t).1.1
  have mem_satU_iff : ∀ (A : Set Work.EKLContract.SL3) (z : Work.EKLContract.SL3),
      z ∈ Work.EKLC6Core.satU (Work.EKLC6Core.Uminus t) A ↔
        ∃ u ∈ Work.EKLC6Core.Uminus t, u * z ∈ A := by
    intro A z
    constructor
    · rintro ⟨u, hu, o, ho, huo⟩
      refine ⟨u⁻¹, (Work.EKLC6Core.Uminus t).inv_mem hu, ?_⟩
      rw [← huo, inv_mul_cancel_left]
      exact ho
    · rintro ⟨u, hu, huz⟩
      exact ⟨u⁻¹, (Work.EKLC6Core.Uminus t).inv_mem hu, u * z, huz,
        inv_mul_cancel_left u z⟩
  have hOsep : ∀ z w : Work.EKLContract.SL3,
      (∀ m, (∃ u ∈ Work.EKLC6Core.Uminus t, u * z ∈ O m) ↔
        (∃ u ∈ Work.EKLC6Core.Uminus t, u * w ∈ O m)) →
      ∃ u ∈ Work.EKLC6Core.Uminus t, w = u * z := by
    intro z w hpat
    have hpat' : ∀ m, z ∈ Work.EKLC6Core.satU (Work.EKLC6Core.Uminus t) (O m) ↔
        w ∈ Work.EKLC6Core.satU (Work.EKLC6Core.Uminus t) (O m) := by
      intro m
      rw [mem_satU_iff, mem_satU_iff]
      exact hpat m
    have hmem : w ∈ Work.EKLC6Core.satU (Work.EKLC6Core.Uminus t) ({z} : Set SL3) :=
      hOsep_sat z w hpat'
    rw [mem_satU_iff] at hmem
    obtain ⟨u, hu, huz⟩ := hmem
    exact ⟨u⁻¹, (Work.EKLC6Core.Uminus t).inv_mem hu, by rw [← huz, inv_mul_cancel_left]⟩
  -- ## 3. The measurability of the clipped cylinders
  have hmeas : ∀ k m, MeasurableSet (Work.EKLC6Core.genCW S O k m) := by
    intro k m
    rw [Work.EKLC6Core.genCW_toCellBase]
    exact Work.EKLC6Core.measurableSet_genC2 S.toCellBase O hOopen k m
  -- ## 4. The rates
  set M : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).sup'
      ⟨((0 : Fin 3), (0 : Fin 3)), Finset.mem_univ _⟩
      (fun p => if t p.1 < t p.2 then Real.exp (t p.1 - t p.2) else 0) with hMdef
  have hM_lt_one : M < 1 := by
    rw [hMdef]
    refine (Finset.sup'_lt_iff _).mpr ?_
    intro p _
    by_cases h : t p.1 < t p.2
    · rw [if_pos h]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    · rw [if_neg h]
      norm_num
  have hM_le : ∀ i j : Fin 3, t i < t j → Real.exp (t i - t j) ≤ M := by
    intro i j hij
    have h := Finset.le_sup'
      (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
      (f := fun p : Fin 3 × Fin 3 =>
        if t p.1 < t p.2 then Real.exp (t p.1 - t p.2) else 0)
      (Finset.mem_univ (i, j))
    rw [if_pos hij] at h
    rwa [hMdef]
  have hM_nonneg : 0 ≤ M := by
    have h := Finset.le_sup'
      (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
      (f := fun p : Fin 3 × Fin 3 =>
        if t p.1 < t p.2 then Real.exp (t p.1 - t p.2) else 0)
      (Finset.mem_univ ((0 : Fin 3), (0 : Fin 3)))
    rw [if_neg (lt_irrefl (t 0))] at h
    rw [hMdef]
    exact h
  set mu : ℝ := (M + 1) / 2 with hmudef
  set lam : ℝ := (M + mu) / 2 with hlamdef
  have hmu0 : 0 < mu := by rw [hmudef]; linarith
  have hmu1 : mu < 1 := by rw [hmudef]; linarith
  have hlam0 : 0 < lam := by rw [hlamdef]; linarith
  have hlammu : lam < mu := by rw [hlamdef]; linarith
  have hlamineq : ∀ i j : Fin 3, t i < t j → Real.exp (t i - t j) ≤ lam := by
    intro i j hij
    have h := hM_le i j hij
    rw [hlamdef]; linarith
  set γ : ℝ := (mu + 1) / 2 with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; linarith
  have hγ1 : γ < 1 := by rw [hγdef]; linarith
  have hmuγ : mu < γ := by rw [hγdef]; linarith
  set δ₀ : ℝ := Real.log (γ / mu) with hδdef
  have hδ0 : 0 < δ₀ := by
    rw [hδdef]
    refine Real.log_pos ?_
    rw [one_lt_div hmu0]
    exact hmuγ
  have hδexp : Real.exp (-δ₀) = mu / γ := by
    rw [hδdef, Real.exp_neg, Real.exp_log (div_pos hγ0 hmu0), inv_div]
  have hmu_eq : mu = γ * Real.exp (-δ₀) := by
    rw [hδexp, mul_div_cancel₀ mu (ne_of_gt hγ0)]
  -- ## 5. The two a.e. inputs along the orbit
  have hdepth := cell_relative_depth_of_disjoint (μ := μ) t hmp hdisj hC hα hthin hγ0 hγ1
  have hcap := ae_injCap_depth (μ := μ) t hmp
  have hVmono : ∀ {r r' : ℝ}, r ≤ r' → V r ⊆ V r' :=
    fun h _ hg i j => lt_of_lt_of_le (hg i j) h
  have hMSigW_eq : Work.EKLC6Core.MSigW S O =
      Work.EKLC6Core.MSigCut (Work.EKLC6Core.Uminus t) Q δ g O := by
    unfold Work.EKLC6Core.MSigW Work.EKLC6Core.MSigCut Work.EKLC6Core.famW
      Work.EKLC6Core.genCW Work.EKLC6Core.genCut Work.EKLC6Core.satU
      Work.EKLC6Core.satUC Work.EKLC6Core.lifted Work.EKLC6Core.liftedC
    rfl
  -- ## 6. The shape containment along the orbit
  have hgood : ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ,
      ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x ∈ Q k →
      Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) (1 * mu ^ n) ⊆
        Work.EKLContract.shape (Work.EKLC6Core.MSigW S O) (Work.EKLC6Core.Uminus t)
          (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) := by
    filter_upwards [hdepth, hcap] with x hdx hcx
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hcx δ₀ hδ0)
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hdx
    refine Filter.eventually_atTop.mpr ⟨max N₁ N₂, fun n hn => ?_⟩
    intro k hk u hu
    have huU : u ∈ Work.EKLC6Core.Uminus t := hu.1
    have huV : u ∈ V (mu ^ n) := by
      intro i j
      have h := hu.2 i j
      rw [one_mul] at h
      exact h
    have hcapn : Real.exp (-(δ₀ * (n : ℝ))) ≤
        Work.EKLC6Core.injCap (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) :=
      hN₁ n (le_trans (le_max_left _ _) hn)
    have hmun : mu ^ n ≤ γ ^ n *
        Work.EKLC6Core.injCap
          (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) := by
      have h1 : mu ^ n = γ ^ n * Real.exp (-(δ₀ * (n : ℝ))) := by
        rw [hmu_eq, mul_pow]
        congr 1
        rw [show Real.exp (-(δ₀ * (n : ℝ))) = Real.exp ((n : ℝ) * (-δ₀)) by ring_nf]
        rw [Real.exp_nat_mul]
      rw [h1]
      exact mul_le_mul_of_nonneg_left hcapn (pow_nonneg hγ0.le n)
    have hdepthn : ∀ v : Work.EKLContract.SL3, v ∈ V (1 * mu ^ n) →
        v • (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) ∈ Q k := by
      intro v hv
      have hv' : v ∈ V (mu ^ n) := by simpa using hv
      exact hN₂ n (le_trans (le_max_right _ _) hn) k hk v (hVmono hmun hv')
    have hatom : u • (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) ∈
        Work.EKLContract.atom (Work.EKLC6Core.MSigCut (Work.EKLC6Core.Uminus t) Q δ g O)
          (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) :=
      Work.EKLC6Core.margin_mem_atom_pointwise (μ := μ)
        (U := Work.EKLC6Core.Uminus t) hopen hdisj hcover
        (fun k => (hδ k).1) (fun k => (hδ k).2) hsub hinj hOopen hOsep_sat
        hk one_pos hmu0 hmu1 hdepthn huU (by rw [one_mul]; exact huV)
    rw [Work.EKLContract.shape]
    exact ⟨huU, by rw [hMSigW_eq]; exact hatom⟩
  -- ## 7. The target
  refine ⟨S, O, lam, mu, hlam0, hlammu, hmu1, hlamineq, hOopen, hOsep, hmeas, ?_⟩
  exact ⟨fun _ => (1 : ℝ), by
    filter_upwards [hgood] with x hx
    exact ⟨one_pos, hx⟩⟩

end

end Work.EKLC6Core
