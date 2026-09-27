import Mathlib
import Submission.Work.EKLC6Core.CellWDefs
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLC6Core.ae_uncrossed_cellsys
import Submission.Work.EKLComp.V_hasBasis_nhds_one

namespace Work.EKLC6Core

open Work.EKLContract MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

/-- The **margin** of `y` inside the cell `Q k`: the largest `r ≤ 2` such that the ball
`V r · y` is contained in `Q k`. -/
def cellMargin (Q : ℕ → Set X3) (k : ℕ) (y : X3) : ℝ :=
  sSup {r : ℝ | 0 < r ∧ r ≤ 2 ∧ ∀ v : SL3, v ∈ V r → v • y ∈ Q k}

/-- Around a point of an open set there is a `V`-ball contained in the set. -/
theorem exists_V_subset_of_mem_open {Q : Set X3} (hQ : IsOpen Q) {y : X3} (hy : y ∈ Q) :
    ∃ r : ℝ, 0 < r ∧ ∀ v : SL3, v ∈ V r → v • y ∈ Q := by
  have hcont : Continuous (fun v : SL3 => v • y) := by fun_prop
  have h1 : {v : SL3 | v • y ∈ Q} ∈ nhds (1 : SL3) :=
    hcont.continuousAt (hQ.mem_nhds (by simpa using hy))
  obtain ⟨r, hr, hsub⟩ := Work.EKLComp.V_hasBasis_nhds_one.mem_iff.mp h1
  exact ⟨r, hr, fun v hv => hsub hv⟩

/-- The defining property of the margin. -/
theorem cellMargin_property {Q : ℕ → Set X3} {k : ℕ} {y : X3} {r : ℝ}
    (hr : r < cellMargin Q k y) (hrnn : 0 ≤ r) : ∀ v : SL3, v ∈ V r → v • y ∈ Q k := by
  by_cases hne : ({r' : ℝ | 0 < r' ∧ r' ≤ 2 ∧ ∀ v : SL3, v ∈ V r' → v • y ∈ Q k}).Nonempty
  · obtain ⟨b, hb, hlt⟩ := (lt_csSup_iff (s := {r' : ℝ | 0 < r' ∧ r' ≤ 2 ∧
      ∀ v : SL3, v ∈ V r' → v • y ∈ Q k}) (by
        refine ⟨2, ?_⟩
        rintro s ⟨-, hs2, -⟩
        exact hs2) hne).mp hr
    intro v hv
    exact hb.2.2 v (Work.Misiurewicz.V_mono (le_of_lt hlt) hv)
  · have h0 : cellMargin Q k y = 0 := by
      rw [cellMargin, Set.not_nonempty_iff_eq_empty.mp hne]
      exact Real.sSup_empty
    linarith [h0, hr, hrnn]

/-- **The reduction.**  If the cell family `Q` has the *relative thinness* property
`μ {y | ∀ k, y ∈ Q k → cellMargin Q k y < ε * injCap y} ≤ C ε ^ α`, and if the capped injectivity
radius along the orbit decays at most geometrically, then the orbit points are `c λ ^ n`-deep
inside their cells. -/
theorem cellW_depth_of_relthin
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (Q : ℕ → Set X3) (hopen : ∀ k, IsOpen (Q k)) (hdisj : ∀ k l, k ≠ l → Disjoint (Q k) (Q l))
    (hcover : μ (⋃ k, Q k)ᶜ = 0)
    {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (hthin : ∀ ε : ℝ, 0 < ε → μ {y : X3 | ∀ k, y ∈ Q k → cellMargin Q k y < ε * injCap y}
        ≤ ENNReal.ofReal (C * ε ^ α))
    {c₂ lam0 : ℝ} (hc2 : 0 < c₂) (hlam0 : 0 < lam0) (hlam1 : lam0 < 1)
    (hgeo : ∀ x : X3, ∀ n : ℕ,
      c₂ * injCap x * lam0 ^ n ≤ injCap ((fun x : X3 => aDiag t • x)^[n] x)) :
    ∃ (c lam : ℝ), 0 < c ∧ 0 < lam ∧ lam < 1 ∧
      ∀ᵐ x ∂μ, ∀ᶠ n in Filter.atTop, ∀ k : ℕ,
        ((fun x : X3 => aDiag t • x)^[n]) x ∈ Q k →
        ∀ v : SL3, v ∈ V (c * lam ^ n) →
          v • (((fun x : X3 => aDiag t • x)^[n]) x) ∈ Q k := by
  classical
  set γ : ℝ := 1 / 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; norm_num
  have hγ1 : γ < 1 := by rw [hγ]; norm_num
  have hγnn : 0 ≤ γ := le_of_lt hγ0
  have hlam : γ * lam0 < 1 := by nlinarith
  refine ⟨1 / 8, γ * lam0, by norm_num, mul_pos hγ0 hlam0, hlam, ?_⟩
  set A : ℕ → ℕ → Set X3 := fun m n =>
    {y : X3 | ∀ k, y ∈ Q k → cellMargin Q k y < (2:ℝ) ^ (m + 1) * γ ^ n * injCap y} with hA
  have hbound : ∀ m n : ℕ, μ (A m n)
      ≤ ENNReal.ofReal ((C * (((2:ℝ) ^ (m + 1)) ^ α)) * (γ ^ α) ^ n) := by
    intro m n
    have hε : 0 < (2:ℝ) ^ (m + 1) * γ ^ n := by positivity
    have h1 := hthin ((2:ℝ) ^ (m + 1) * γ ^ n) hε
    have h2 : (((2:ℝ) ^ (m + 1) * γ ^ n) ^ α) = (((2:ℝ) ^ (m + 1)) ^ α) * (γ ^ α) ^ n := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast γ n,
        ← Real.rpow_mul hγnn (n : ℝ) α, mul_comm (n : ℝ) α, Real.rpow_mul hγnn α (n : ℝ),
        Real.rpow_natCast]
    rw [h2] at h1
    refine le_trans h1 (le_of_eq (congrArg ENNReal.ofReal (by ring)))
  have hγlt : γ ^ α < 1 := Real.rpow_lt_one hγnn hγ1 hα
  have hγnn' : 0 ≤ γ ^ α := Real.rpow_nonneg hγnn α
  have hnull : ∀ m : ℕ, μ (⋂ N : ℕ, ⋃ n ≥ N,
      ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' (A m n)) = 0 := by
    intro m
    refine geometric_borel_cantelli μ
      (fun n => ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' (A m n))
      (c := C * (((2:ℝ) ^ (m + 1)) ^ α)) (r := γ ^ α)
      (mul_nonneg (le_of_lt hC) (Real.rpow_nonneg (by positivity) α)) hγnn' hγlt ?_
    intro n
    exact le_trans ((hmp.iterate n).measure_preimage_le (A m n)) (hbound m n)
  have hE : μ (⋃ m : ℕ, ⋂ N : ℕ, ⋃ n ≥ N,
      ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' (A m n)) = 0 :=
    measure_iUnion_null fun m => hnull m
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun x hx => ?_) hE
  by_contra hxE
  have hpowle : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      calc k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by ring
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1/4 : ℝ) ≤ (2:ℝ) ^ (m + 1) * c₂ * injCap x := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((1/4 : ℝ) / (c₂ * injCap x))
    refine ⟨n + 2, ?_⟩
    have hpos : 0 < c₂ * injCap x := mul_pos hc2 (injCap_pos x)
    have hle : ((n : ℝ) + 1) ≤ (2:ℝ) ^ (n + 3) := by
      have hcast : ((n + 3 : ℕ) : ℝ) ≤ ((2 ^ (n + 3) : ℕ) : ℝ) := by
        exact_mod_cast hpowle (n + 3)
      push_cast at hcast
      linarith
    have hkey : ((1/4 : ℝ) / (c₂ * injCap x)) ≤ (2:ℝ) ^ (n + 3) := by
      linarith [le_of_lt hn, hle]
    have h3 : (1/4 : ℝ) ≤ (2:ℝ) ^ (n + 3) * (c₂ * injCap x) := by
      have := mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
    rw [show n + 2 + 1 = n + 3 by omega]
    linarith [h3]
  have hxev : ∀ᶠ n in Filter.atTop, x ∉ ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' (A m n) := by
    by_contra hcon
    refine hxE (Set.mem_iUnion.mpr ⟨m, ?_⟩)
    rw [Filter.not_eventually, Filter.frequently_atTop] at hcon
    refine Set.mem_iInter.mpr fun N => ?_
    obtain ⟨n, hnN, hn⟩ := hcon N
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hnN, by simpa using hn⟩⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hxev
  have hfin : ∀ᶠ n in Filter.atTop, ∀ k' : ℕ,
      ((fun x : X3 => aDiag t • x)^[n]) x ∈ Q k' →
      ∀ v : SL3, v ∈ V ((1/8) * (γ * lam0) ^ n) →
        v • (((fun x : X3 => aDiag t • x)^[n]) x) ∈ Q k' := by
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    intro k' hk'
    have hnotmem : ((fun x : X3 => aDiag t • x)^[n]) x ∉ A m n := by
      simpa using hN n hn
    simp only [hA, Set.mem_ofPred_eq, not_forall] at hnotmem
    obtain ⟨k, hk, hmg⟩ := hnotmem
    push_neg at hmg
    have hgeo' := hgeo x n
    have hbig : (1/4 : ℝ) * (γ * lam0) ^ n
        ≤ cellMargin Q k (((fun x : X3 => aDiag t • x)^[n]) x) := by
      have hnn : 0 ≤ (γ * lam0) ^ n := by positivity
      have h2 : (1/4 : ℝ) * (γ * lam0) ^ n ≤
          (2:ℝ) ^ (m + 1) * c₂ * injCap x * (γ * lam0) ^ n := by nlinarith [hm, hnn]
      refine le_trans h2 (le_trans ?_ hmg)
      have hsplit : (2:ℝ) ^ (m + 1) * c₂ * injCap x * (γ * lam0) ^ n
          = (2:ℝ) ^ (m + 1) * γ ^ n * (c₂ * injCap x * lam0 ^ n) := by ring
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hgeo' (by positivity)
    have hsmall : ((1/8 : ℝ) * (γ * lam0) ^ n)
        < cellMargin Q k (((fun x : X3 => aDiag t • x)^[n]) x) := by
      have : 0 < (γ * lam0) ^ n := by positivity
      nlinarith [hbig, this]
    have hprop := cellMargin_property hsmall (by positivity)
    have hk_eq : k' = k := by
      by_contra hne
      exact absurd (Set.disjoint_left.mp (hdisj k' k hne) hk' hk) (by simp)
    subst hk_eq
    exact hprop
  exact absurd hfin hx

end

end Work.EKLC6Core
