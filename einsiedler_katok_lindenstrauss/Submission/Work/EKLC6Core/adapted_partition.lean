import Mathlib
import Submission.Work.EKLC6Core.thin_boundary_partition
import Submission.Work.EKLC6Core.thin_pattern_partition
import Submission.Work.EKLC6Core.cut_defs
import Submission.Work.EKLC6Core.cut_cells
import Submission.Work.EKLC6Core.inv_mul_mem_Gamma3_eq
import Submission.Work.EKLC6Core.uniform_injective_V_X3
import Submission.Work.EKLComp.inv_mem_V
import Submission.Work.EKLContract.Lemmas.Gamma3Facts

/-!
# `Work.EKLC6Core.adapted_partition`

The partition of `X₃ = SL₃(ℝ)/SL₃(ℤ)` adapted to the lattice `Γ₃`, used as step 1 of the "cut"
construction (Pisa 7.37/7.38, see `CUT_PLAN.md`).

For every probability measure `μ` on `X₃` and every `ε > 0` there are finitely many pairwise
disjoint *open* sets `Q i`, group elements `g i`, and constants `ρ, c > 0` such that

* `Q i` is a neighbourhood of its own "centre" `mkX (g i)` and is contained in the `V ρ`-ball
  around that centre;
* the centres are *`Γ₃`-free at scale `60 ρ`*: `g i γ (g i)⁻¹ ∈ V (60 ρ)` for `γ ∈ Γ₃` forces
  `γ = 1` (equivalently: no conjugate of a nontrivial element of `Γ₃` is within `V (60 ρ)` of the
  identity);
* the cells cover all but `< ε` of the `μ`-mass;
* the total `V η`-collar of the union of the cell frontiers is at most `c η`.

The construction: pick a scale `η` at which the "bad" set of points whose stabiliser meets `V η`
nontrivially has measure `< ε/8` (`badPt_measure_small`), set `ρ = η/60`, and apply the
thin-boundary partition `thin_boundary_partition` with a very small ball radius `s = ρ/100`.  A
piece `P i` of that partition lies in a `V s`-ball, so *any* two of its points differ by an
element of `V (12 s) ⊆ V ρ`; hence *any* point of `P i` can serve as the centre of the cell
`interior (P i)`.  Choosing, for every piece that has such a point, a centre outside the bad set
and passing to the subfamily of pieces whose interior meets the good set gives the cells.

The two ingredients `badPt_measure_small` (the bad set is small) and `thin_boundary_partition`
(measurable partition with thin boundary and small-diameter pieces) are independent of each other
and are proved in the corresponding modules.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
open Work.EKLContract

/-- The set of "bad lifts" at scale `η`: elements of `SL₃(ℝ)` having a nontrivial `Γ₃`-conjugate
within the entrywise neighbourhood `V η` of the identity. -/
def badLift (η : ℝ) : Set SL3 :=
  {g : SL3 | ∃ γ ∈ Γ3, γ ≠ 1 ∧ g * γ * g⁻¹ ∈ V η}

/-- The corresponding set of "bad points" of `X₃`: those cosets `x = gΓ₃` admitting a lift
`g` with `∃ γ ∈ Γ₃ \ {1}, g γ g⁻¹ ∈ V η`.  This is exactly the set of points whose stabiliser
`g Γ₃ g⁻¹` meets `V η` off the identity, so that a point *outside* `badPt η` has injectivity
radius `η` in the sense of the conclusion of `adapted_partition`. -/
def badPt (η : ℝ) : Set X3 := mkX '' (badLift η)

theorem badPt_mono {η η' : ℝ} (h : η ≤ η') : badPt η ⊆ badPt η' := by
  rintro x ⟨g, hg, rfl⟩
  obtain ⟨γ, hγ, hne, hm⟩ := hg
  exact ⟨g, ⟨γ, hγ, hne, fun i j => lt_of_lt_of_le (hm i j) h⟩, rfl⟩

/-- The entrywise neighbourhoods `V δ` are monotone in `δ`. -/
theorem adapted_V_mono {a b : ℝ} (h : a ≤ b) : V a ⊆ V b :=
  fun g hg i j => lt_of_lt_of_le (hg i j) h

/-- The bad set is open, hence Borel: locally it is the preimage of the open set `V η` under
`g ↦ g γ g⁻¹` for the (bounded, hence fixed) witness `γ`, and `mkX` is an open map. -/
theorem isOpen_badLift (η : ℝ) (hη : 0 < η) : IsOpen (badLift η) := by
  rw [isOpen_iff_mem_nhds]
  rintro g ⟨γ, hγ, hne, hgγ⟩
  have hcont : Continuous (fun g' : SL3 => g' * γ * g'⁻¹) :=
    (continuous_id.mul continuous_const).mul continuous_inv
  have hopen : IsOpen ((fun g' : SL3 => g' * γ * g'⁻¹) ⁻¹' (V η)) :=
    (Work.EKLContract.Lemmas.V_open_one η hη).1.preimage hcont
  refine Filter.mem_of_superset (hopen.mem_nhds hgγ) ?_
  intro g' hg'
  exact ⟨γ, hγ, hne, hg'⟩

/-- The bad set of points is open, since `mkX` is an open map. -/
theorem isOpen_badPt (η : ℝ) (hη : 0 < η) : IsOpen (badPt η) :=
  isOpenMap_mkX _ (isOpen_badLift η hη)

/-- A point of a set which is not in its interior lies on its frontier. -/
theorem adapted_mem_frontier {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}
    (hx : x ∈ s) (h : x ∉ interior s) : x ∈ frontier s := by
  rw [← closure_sdiff_interior]
  exact ⟨subset_closure hx, h⟩

/-- **Smallness of the bad set.**  The set `badPt η` decreases to `∅` as `η ↓ 0` (a discrete
subgroup has isolated identity), so by continuity from above for the finite measure `μ` its
measure tends to `0`. -/
theorem badPt_measure_small_aux (μ : Measure X3) [IsFiniteMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ μ (badPt η) < ENNReal.ofReal ε := by
  classical
  set S : ℕ → Set X3 := fun n => badPt (1/((n:ℝ)+1)) with hS
  have hSpos : ∀ n : ℕ, (0:ℝ) < 1/((n:ℝ)+1) := fun n => one_div_pos.mpr (by positivity)
  have hsanti : Antitone S := by
    intro i j hij
    rw [hS]
    apply badPt_mono
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.succ_le_succ hij
  have hmeas : ∀ n, NullMeasurableSet (S n) μ := by
    intro n
    rw [hS]
    exact (isOpen_badPt _ (hSpos n)).nullMeasurableSet
  -- The intersection of the bad sets is empty: a point has positive injectivity radius.
  have hnil : (⋂ n, S n) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Set.mem_iInter] at hx
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective x
    have hstep : ∀ n : ℕ, ∃ e : SL3, e ∈ Γ3 ∧ e ≠ 1 ∧ g₀ * e * g₀⁻¹ ∈ V (1/((n:ℝ)+1)) := by
      intro n
      have hxn : x ∈ badPt (1/((n:ℝ)+1)) := hx n
      obtain ⟨g, hg, hgm⟩ := hxn
      obtain ⟨γ, hγ, hne, hm⟩ := hg
      have hδΓ : g₀⁻¹ * g ∈ Γ3 := QuotientGroup.eq.mp (hg₀.trans hgm.symm)
      refine ⟨(g₀⁻¹ * g) * γ * (g₀⁻¹ * g)⁻¹,
        Γ3.mul_mem (Γ3.mul_mem hδΓ hγ) (Γ3.inv_mem hδΓ), ?_, ?_⟩
      · intro h1
        apply hne
        have h2 := congrArg (fun z => (g₀⁻¹ * g)⁻¹ * z * (g₀⁻¹ * g)) h1
        simpa [mul_assoc] using h2
      · rw [show g₀ * ((g₀⁻¹ * g) * γ * (g₀⁻¹ * g)⁻¹) * g₀⁻¹ = g * γ * g⁻¹ by group]
        exact hm
    choose e heΓ hene hemem using hstep
    have htend : Tendsto (fun n => g₀ * e n * g₀⁻¹) atTop (𝓝 1) :=
      tendsto_of_mem_V tendsto_one_div_add_atTop_nhds_zero_nat (fun n => hemem n)
    have htend2 : Tendsto (fun n => e n) atTop (𝓝 (1 : SL3)) := by
      have h1 : Tendsto (fun n => g₀⁻¹ * (g₀ * e n * g₀⁻¹) * g₀) atTop (𝓝 (g₀⁻¹ * 1 * g₀)) :=
        (tendsto_const_nhds.mul htend).mul tendsto_const_nhds
      have h2 : g₀⁻¹ * (1 : SL3) * g₀ = 1 := by group
      rw [h2] at h1
      simpa [mul_assoc] using h1
    have hV : V ((1:ℝ)/2) ∈ 𝓝 (1 : SL3) :=
      (Work.EKLContract.Lemmas.V_open_one ((1:ℝ)/2) (by norm_num)).1.mem_nhds
        (Work.EKLContract.Lemmas.V_open_one ((1:ℝ)/2) (by norm_num)).2
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htend2.eventually hV)
    exact hene N (eq_one_of_mem_Γ3_mem_V_half (e N) (heΓ N) (hN N le_rfl))
  have hfin : ∃ n, μ (S n) ≠ ∞ := ⟨0, measure_ne_top μ _⟩
  have htend : Tendsto (fun n => μ (S n)) atTop (𝓝 (μ (⋂ n, S n))) :=
    tendsto_measure_iInter_atTop hmeas hsanti hfin
  rw [hnil, measure_empty] at htend
  rw [ENNReal.tendsto_nhds_zero] at htend
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (htend (ENNReal.ofReal (ε/2)) (ENNReal.ofReal_pos.mpr (by linarith)))
  refine ⟨1/((N:ℝ)+1), one_div_pos.mpr (by positivity), ?_⟩
  refine lt_of_le_of_lt (hN N le_rfl) ?_
  rw [ENNReal.ofReal_lt_ofReal_iff hε]; linarith

/-- Two points of a `V s`-ball around `x` differ by an element of `V (s + 10 s + 3 s · 10 s)`. -/
theorem adapted_pair_Vball {x c z : X3} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hc : c ∈ (fun u : SL3 => u • x) '' (V s)) (hz : z ∈ (fun u : SL3 => u • x) '' (V s)) :
    z ∈ (fun u : SL3 => u • c) '' (V (s + 10 * s + 3 * s * (10 * s))) := by
  obtain ⟨a, ha, rfl⟩ := hc
  obtain ⟨b, hb, rfl⟩ := hz
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · have hainv : a⁻¹ ∈ V (10 * s) := Work.EKLComp.inv_mem_V hs hs1 ha
    intro i j
    have h := Work.EKLRelCross.entries_mul_sub_one_le
      (A := ((b : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      (B := ((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j
      (fun k l => hb k l) (fun k l => hainv k l) (le_of_lt hs) (by linarith)
    rw [← Matrix.SpecialLinearGroup.coe_mul] at h
    exact h
  · simp only [mul_smul, inv_smul_smul]

theorem adapted_partition (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (Q : Fin N → Set Work.EKLContract.X3) (g : Fin N → Work.EKLContract.SL3)
      (ρ c : ℝ),
      0 < ρ ∧ 0 < c ∧ (∀ i, IsOpen (Q i)) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
      (∀ i, Work.EKLContract.mkX (g i) ∈ Q i) ∧
      (∀ i, Q i ⊆ (fun u : Work.EKLContract.SL3 => u • Work.EKLContract.mkX (g i)) ''
          (Work.EKLContract.V ρ)) ∧
      (∀ i (γ : Work.EKLContract.SL3), γ ∈ Work.EKLContract.Γ3 →
        g i * γ * (g i)⁻¹ ∈ Work.EKLContract.V (60 * ρ) → γ = 1) ∧
      μ ((⋃ i, Q i))ᶜ < ENNReal.ofReal ε ∧
      (∀ η : ℝ, 0 < η → μ (⋃ i, Work.EKLC6Core.VThick η (frontier (Q i))) ≤
        ENNReal.ofReal (c * η)) := by
  classical
  haveI : IsFiniteMeasure μ := inferInstance
  obtain ⟨η₁, hη₁pos, hη₁small⟩ := badPt_measure_small_aux μ (ε/8) (by linarith)
  set η₀ : ℝ := min η₁ 1 with hη₀def
  have hη₀pos : 0 < η₀ := lt_min hη₁pos one_pos
  have hη₀le1 : η₀ ≤ 1 := min_le_right _ _
  have hη₀le : η₀ ≤ η₁ := min_le_left _ _
  have hbad : μ (badPt η₀) < ENNReal.ofReal (ε/8) :=
    lt_of_le_of_lt (measure_mono (badPt_mono hη₀le)) hη₁small
  set ρ : ℝ := η₀ / 60 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρle1 : ρ ≤ 1 := by rw [hρdef]; linarith
  set s : ℝ := ρ / 100 with hsdef
  have hspos : 0 < s := by rw [hsdef]; linarith
  have hsle1 : s ≤ 1 := by rw [hsdef]; linarith
  have h60 : 60 * ρ = η₀ := by rw [hρdef]; ring
  have hbig : s + 10*s + 3*s*(10*s) ≤ ρ := by
    rw [hsdef]; nlinarith [hρpos, hρle1]
  obtain ⟨N, P, i₀, c, hcpos, hPmeas, hPdisj, hPcov, hPsub, hPi₀, hPthin⟩ :=
    thin_boundary_partition μ (ε/8) s (by linarith) hspos
  have hUF : μ (⋃ i, frontier (P i)) = 0 :=
    measure_iUnion_frontier_eq_zero P hcpos (fun η hη => by
      simpa only [VThick_def] using hPthin η hη)
  let Idx := {i : Fin N // i ≠ i₀ ∧ (interior (P i) ∩ (badPt η₀)ᶜ).Nonempty}
  let e : Fin (Fintype.card Idx) ≃ Idx := (Fintype.equivFin Idx).symm
  let cc : Fin (Fintype.card Idx) → X3 := fun j => Classical.choose (e j).2.2
  have hcc_int : ∀ j, cc j ∈ interior (P (e j).1) :=
    fun j => (Classical.choose_spec (e j).2.2).1
  have hcc_good : ∀ j, cc j ∉ badPt η₀ := fun j => (Classical.choose_spec (e j).2.2).2
  let g : Fin (Fintype.card Idx) → SL3 := fun j => Quotient.out (cc j)
  have hg : ∀ j, mkX (g j) = cc j := fun j => Quotient.out_eq (cc j)
  refine ⟨Fintype.card Idx, (fun j => interior (P (e j).1)), g, ρ, c,
    hρpos, hcpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; exact isOpen_interior
  · intro i j hij
    have he : (e i).1 ≠ (e j).1 := by
      intro h
      exact hij (e.injective (Subtype.ext h))
    exact (hPdisj (e i).1 (e j).1 he).mono interior_subset interior_subset
  · intro j
    rw [hg j]; exact hcc_int j
  · intro j z hz
    have hne : (e j).1 ≠ i₀ := (e j).2.1
    obtain ⟨x, hx⟩ := hPsub (e j).1 hne
    have hcx : cc j ∈ (fun u : SL3 => u • x) '' (V s) := hx (interior_subset (hcc_int j))
    have hzx : z ∈ (fun u : SL3 => u • x) '' (V s) := hx (interior_subset hz)
    obtain ⟨u, hu, huz⟩ := adapted_pair_Vball hspos hsle1 hcx hzx
    refine ⟨u, adapted_V_mono hbig hu, ?_⟩
    rw [hg j]; exact huz
  · intro j γ hγ hm
    have hgood : mkX (g j) ∉ badPt η₀ := by rw [hg j]; exact hcc_good j
    rw [h60] at hm
    by_contra hne
    exact hgood ⟨g j, ⟨γ, hγ, hne, hm⟩, rfl⟩
  · have hsub : (⋃ j, (fun j => interior (P (e j).1)) j)ᶜ ⊆ badPt η₀ ∪ P i₀ ∪ ⋃ i, frontier (P i) := by
      intro x hx
      have hxall : x ∈ ⋃ i, P i := by rw [hPcov]; trivial
      obtain ⟨j₀, hj₀⟩ := mem_iUnion.mp hxall
      by_cases hji : j₀ = i₀
      · exact Or.inl (Or.inr (hji ▸ hj₀))
      · by_cases hk : (interior (P j₀) ∩ (badPt η₀)ᶜ).Nonempty
        · obtain ⟨j, hj⟩ : ∃ j, e j = ⟨j₀, hji, hk⟩ := ⟨e.symm ⟨j₀, hji, hk⟩, by simp⟩
          have hxj : x ∉ interior (P j₀) := by
            intro hcon
            exact hx (mem_iUnion.mpr ⟨j, by rw [hj]; exact hcon⟩)
          exact Or.inr (mem_iUnion.mpr ⟨j₀, adapted_mem_frontier hj₀ hxj⟩)
        · have hsub2 : interior (P j₀) ⊆ badPt η₀ := by
            intro y hy
            by_contra hyb
            exact hk ⟨y, hy, hyb⟩
          by_cases hxint : x ∈ interior (P j₀)
          · exact Or.inl (Or.inl (hsub2 hxint))
          · exact Or.inr (mem_iUnion.mpr ⟨j₀, adapted_mem_frontier hj₀ hxint⟩)
    have hmain : μ ((⋃ j, (fun j => interior (P (e j).1)) j)ᶜ)
        ≤ (ENNReal.ofReal (ε/8) + ENNReal.ofReal (ε/8)) + μ (⋃ i, frontier (P i)) := by
      calc μ ((⋃ j, (fun j => interior (P (e j).1)) j)ᶜ)
          ≤ μ (badPt η₀ ∪ P i₀ ∪ ⋃ i, frontier (P i)) := measure_mono hsub
        _ ≤ μ (badPt η₀ ∪ P i₀) + μ (⋃ i, frontier (P i)) := measure_union_le _ _
        _ ≤ (μ (badPt η₀) + μ (P i₀)) + μ (⋃ i, frontier (P i)) :=
            add_le_add (measure_union_le _ _) le_rfl
        _ ≤ (ENNReal.ofReal (ε/8) + ENNReal.ofReal (ε/8)) + μ (⋃ i, frontier (P i)) :=
            add_le_add (add_le_add (le_of_lt hbad) (le_of_lt hPi₀)) le_rfl
    refine lt_of_le_of_lt hmain ?_
    rw [hUF, add_zero, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    rw [ENNReal.ofReal_lt_ofReal_iff hε]
    linarith
  · intro η hη
    have hsub : (⋃ j, VThick η (frontier ((fun j => interior (P (e j).1)) j)))
        ⊆ (⋃ i, VThick η (frontier (P i))) := by
      intro z hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      refine mem_iUnion.mpr ⟨(e j).1, ?_⟩
      exact VThick_mono_right frontier_interior_subset η hj
    calc μ (⋃ j, VThick η (frontier ((fun j => interior (P (e j).1)) j)))
        ≤ μ (⋃ i, VThick η (frontier (P i))) := measure_mono hsub
      _ ≤ ENNReal.ofReal (c * η) := by
          simpa only [VThick_def] using hPthin η hη

end Work.EKLC6Core
