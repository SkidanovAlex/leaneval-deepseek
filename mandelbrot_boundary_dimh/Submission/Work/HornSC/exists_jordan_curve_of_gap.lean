import Mathlib
import Submission.Work.HornSC.Tools
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.exists_jordan_curve_of_cellUnion
import Submission.Work.HornSC.DilInterior.cellUnion_subset_interior_dil3
import Submission.Work.HornSC.CellDistBound.dist_le_of_mem_cellUnion_dil3
import Submission.Work.HornSC.ScaleComponent.isBounded_connectedComponentIn_mul

namespace Work.HornSC

open Set

open Work.HornSC.CellBoundaryJordan Work.HornSC.DilInterior Work.HornSC.CellDistBound
  Work.HornSC.ScaleComponent

/-! ## Auxiliary lemmas -/

/-- The connected component of a point in a closed set is closed. -/
lemma isClosed_connectedComponentIn_of_isClosed {S : Set ℂ} (hS : IsClosed S) (a : ℂ) :
    IsClosed (connectedComponentIn S a) := by
  by_cases ha : a ∈ S
  · have h1 : IsPreconnected (closure (connectedComponentIn S a)) :=
      isPreconnected_connectedComponentIn.closure
    have h2 : a ∈ closure (connectedComponentIn S a) :=
      subset_closure (mem_connectedComponentIn ha)
    have h3 : closure (connectedComponentIn S a) ⊆ S :=
      calc closure (connectedComponentIn S a) ⊆ closure S :=
            closure_mono (connectedComponentIn_subset S a)
        _ = S := hS.closure_eq
    exact isClosed_of_closure_subset (h1.subset_connectedComponentIn h2 h3)
  · rw [connectedComponentIn_eq_empty ha]
    exact isClosed_empty

/-- A lattice cell is convex. -/
lemma convex_cell (p : ℤ × ℤ) : Convex ℝ (cell p) := by
  rw [convex_iff_forall_pos]
  rintro x ⟨hx1, hx2, hx3, hx4⟩ y ⟨hy1, hy2, hy3, hy4⟩ a b ha hb hab
  have ha0 : (0 : ℝ) ≤ a := le_of_lt ha
  have hb0 : (0 : ℝ) ≤ b := le_of_lt hb
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  · have h1 : a * (p.1 : ℝ) ≤ a * x.re := mul_le_mul_of_nonneg_left hx1 ha0
    have h2 : b * (p.1 : ℝ) ≤ b * y.re := mul_le_mul_of_nonneg_left hy1 hb0
    have h3 : (p.1 : ℝ) = a * (p.1 : ℝ) + b * (p.1 : ℝ) := by rw [← add_mul, hab, one_mul]
    linarith
  · have h1 : a * x.re ≤ a * ((p.1 : ℝ) + 1) := mul_le_mul_of_nonneg_left hx2 ha0
    have h2 : b * y.re ≤ b * ((p.1 : ℝ) + 1) := mul_le_mul_of_nonneg_left hy2 hb0
    have h3 : ((p.1 : ℝ) + 1) = a * ((p.1 : ℝ) + 1) + b * ((p.1 : ℝ) + 1) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · have h1 : a * (p.2 : ℝ) ≤ a * x.im := mul_le_mul_of_nonneg_left hx3 ha0
    have h2 : b * (p.2 : ℝ) ≤ b * y.im := mul_le_mul_of_nonneg_left hy3 hb0
    have h3 : (p.2 : ℝ) = a * (p.2 : ℝ) + b * (p.2 : ℝ) := by rw [← add_mul, hab, one_mul]
    linarith
  · have h1 : a * x.im ≤ a * ((p.2 : ℝ) + 1) := mul_le_mul_of_nonneg_left hx4 ha0
    have h2 : b * y.im ≤ b * ((p.2 : ℝ) + 1) := mul_le_mul_of_nonneg_left hy4 hb0
    have h3 : ((p.2 : ℝ) + 1) = a * ((p.2 : ℝ) + 1) + b * ((p.2 : ℝ) + 1) := by
      rw [← add_mul, hab, one_mul]
    linarith

/-- The finite family of lattice cells meeting `C` inside the box of cells `[-N,N]²`. -/
noncomputable def cellsMeeting (N : ℕ) (C : Set ℂ) : Finset (ℤ × ℤ) := by
  classical
  exact (Finset.Icc (-(N : ℤ), -(N : ℤ)) (N, N)).filter (fun p => (cell p ∩ C).Nonempty)

lemma mem_cellsMeeting {N : ℕ} {C : Set ℂ} {p : ℤ × ℤ} :
    p ∈ cellsMeeting N C ↔
      p ∈ Finset.Icc (-(N : ℤ), -(N : ℤ)) (N, N) ∧ (cell p ∩ C).Nonempty := by
  classical
  rw [cellsMeeting]
  exact Finset.mem_filter

lemma cellsMeeting_spec {N : ℕ} {C : Set ℂ} {p : ℤ × ℤ} (hp : p ∈ cellsMeeting N C) :
    (cell p ∩ C).Nonempty := (mem_cellsMeeting.mp hp).2

/-- The square `[-N,N]²` of the plane. -/
def boxSet (N : ℕ) : Set ℂ :=
  {z : ℂ | -(N : ℝ) ≤ z.re ∧ z.re ≤ (N : ℝ) ∧ -(N : ℝ) ≤ z.im ∧ z.im ≤ (N : ℝ)}

/-- Every point of the box `[-N,N]²` lies in one of the cells with indices in `[-N,N]²`. -/
lemma exists_cell_mem_Icc {N : ℕ} {z : ℂ} (hz : z ∈ boxSet N) :
    ∃ p : ℤ × ℤ, p ∈ Finset.Icc (-(N : ℤ), -(N : ℤ)) (N, N) ∧ z ∈ cell p := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have e1 : ⌊(-(N : ℝ))⌋ = -(N : ℤ) := by rw [Int.floor_neg, Int.ceil_natCast]
  have e2 : ⌊((N : ℝ))⌋ = (N : ℤ) := Int.floor_intCast N
  refine ⟨(⌊z.re⌋, ⌊z.im⌋), ?_, ?_⟩
  · rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [Prod.mk_le_mk]
      exact ⟨le_trans (le_of_eq e1.symm) (Int.floor_mono h1),
        le_trans (le_of_eq e1.symm) (Int.floor_mono h3)⟩
    · rw [Prod.mk_le_mk]
      exact ⟨le_trans (Int.floor_mono h2) (le_of_eq e2),
        le_trans (Int.floor_mono h4) (le_of_eq e2)⟩
  · refine mem_cell.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact Int.floor_le z.re
    · exact le_of_lt (Int.lt_floor_add_one z.re)
    · exact Int.floor_le z.im
    · exact le_of_lt (Int.lt_floor_add_one z.im)

lemma boxSet_subset_cellUnion (N : ℕ) :
    boxSet N ⊆ cellUnion (Finset.Icc (-(N : ℤ), -(N : ℤ)) (N, N)) := by
  intro z hz
  obtain ⟨p, hp, hzp⟩ := exists_cell_mem_Icc hz
  exact cell_subset_cellUnion hp hzp

/-- If `C` is contained in the box of cells `[-N,N]²`, then `C` is covered by the cells of that
box which meet `C`. -/
lemma subset_cellUnion_cellsMeeting {N : ℕ} {C : Set ℂ} (hC : C ⊆ boxSet N) :
    C ⊆ cellUnion (cellsMeeting N C) := by
  intro c hc
  obtain ⟨p, hp, hcp⟩ := exists_cell_mem_Icc (hC hc)
  exact cell_subset_cellUnion (mem_cellsMeeting.mpr ⟨hp, ⟨c, hcp, hc⟩⟩) hcp

lemma cellsMeeting_nonempty {N : ℕ} {C : Set ℂ} (hne : C.Nonempty) (hC : C ⊆ boxSet N) :
    (cellsMeeting N C).Nonempty := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨p, hp, hcp⟩ := exists_cell_mem_Icc (hC hc)
  exact ⟨p, mem_cellsMeeting.mpr ⟨hp, ⟨c, hcp, hc⟩⟩⟩

theorem exists_jordan_curve_of_gap {S S' : Set ℂ} (hS : IsCompact S) (hSne : S.Nonempty)
    (hS' : IsClosed S') (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ S', δ ≤ dist s s')
    {a : ℂ} (ha : a ∈ S) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧ Set.range γ ⊆ (S ∪ S')ᶜ ∧
      a ∉ Set.range γ ∧ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) := by
  classical
  obtain ⟨δ, hδpos, hgap⟩ := hgap
  -- the mesh of the lattice
  have hsqrt2 : Real.sqrt 2 < (2 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
    norm_num
  -- scale everything down by `h`, so that the unit lattice is fine enough
  have hδ8 : 0 < δ / 8 := by positivity
  set h : ℝ := δ / 8 with hhdef
  have hhpos : 0 < h := by rw [hhdef]; exact hδ8
  have hhgap : 2 * Real.sqrt 2 < δ / h := by
    have hdiv : δ / h = 8 := by
      rw [hhdef]; field_simp
    rw [hdiv]
    nlinarith [hsqrt2]
  set c : ℂ := ((h⁻¹ : ℝ) : ℂ) with hcdef
  have hcne : c ≠ 0 := by
    simp only [hcdef, ne_eq, Complex.ofReal_eq_zero]
    exact inv_ne_zero (ne_of_gt hhpos)
  have hcinv : c * ((h : ℝ) : ℂ) = 1 := by
    rw [hcdef, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hhpos), Complex.ofReal_one]
  -- scaled data
  set S₁ : Set ℂ := (fun z : ℂ => c * z) '' S with hS₁def
  set S₁' : Set ℂ := (fun z : ℂ => c * z) '' S' with hS₁'def
  set a₁ : ℂ := c * a with ha₁def
  have hS₁cpt : IsCompact S₁ := hS.image (by fun_prop)
  have hS₁ne : S₁.Nonempty := hSne.image _
  have ha₁ : a₁ ∈ S₁ := ⟨a, ha, rfl⟩
  -- the gap survives the scaling
  have hgap₁ : ∀ y ∈ S₁, ∀ z ∈ S₁', δ / h ≤ dist y z := by
    rintro y ⟨u, hu, rfl⟩ z ⟨v, hv, rfl⟩
    have h1 : dist (c * u) (c * v) = h⁻¹ * dist u v := by
      have hy : c * u = (h⁻¹ : ℝ) • u := by rw [hcdef, ← Complex.real_smul]
      have hz : c * v = (h⁻¹ : ℝ) • v := by rw [hcdef, ← Complex.real_smul]
      rw [hy, hz, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hhpos)]
    rw [h1]
    have h2 : h⁻¹ * δ ≤ h⁻¹ * dist u v :=
      mul_le_mul_of_nonneg_left (hgap u hu v hv) (le_of_lt (inv_pos.mpr hhpos))
    calc δ / h = h⁻¹ * δ := by rw [div_eq_inv_mul]
      _ ≤ h⁻¹ * dist u v := h2
  -- a box containing the scaled set
  obtain ⟨R, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ S₁ ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hS₁cpt.isBounded
    exact ⟨max R 0, le_max_right _ _, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, S₁ ⊆ boxSet N := by
    refine ⟨⌈R⌉₊, fun z hz => ?_⟩
    have hzR : ‖z‖ ≤ R := by
      have := hR.2 hz
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hre : |z.re| ≤ R := le_trans (Complex.abs_re_le_norm z) hzR
    have him : |z.im| ≤ R := le_trans (Complex.abs_im_le_norm z) hzR
    have hN' : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
    exact ⟨by linarith [(abs_le.mp hre).1, hN'], by linarith [(abs_le.mp hre).2, hN'],
      by linarith [(abs_le.mp him).1, hN'], by linarith [(abs_le.mp him).2, hN']⟩
  -- the cells meeting `S₁`
  set A : Finset (ℤ × ℤ) := cellsMeeting N S₁ with hAdef
  have hA_sub : S₁ ⊆ cellUnion A := subset_cellUnion_cellsMeeting hN
  have hA_spec : ∀ p ∈ A, (cell p ∩ S₁).Nonempty := fun p hp => cellsMeeting_spec hp
  have hAne : A.Nonempty := cellsMeeting_nonempty hS₁ne hN
  have hS₁_int : S₁ ⊆ interior (cellUnion (dil3 A)) :=
    fun z hz => cellUnion_subset_interior_dil3 A (hA_sub hz)
  -- the component of `a₁` in the dilated union
  have ha₁P : a₁ ∈ cellUnion (dil3 A) := cellUnion_subset_dil3 A (hA_sub ha₁)
  set P₀ : Set ℂ := connectedComponentIn (cellUnion (dil3 A)) a₁ with hP₀def
  have hP₀conn : IsConnected P₀ := isConnected_connectedComponentIn_iff.mpr ha₁P
  have hP₀sub : P₀ ⊆ cellUnion (dil3 A) := connectedComponentIn_subset _ _
  have hP₀cl : IsClosed P₀ :=
    isClosed_connectedComponentIn_of_isClosed (isClosed_cellUnion _) a₁
  -- the cells contained in `P₀`
  set A₀ : Finset (ℤ × ℤ) := (dil3 A).filter (fun p => cell p ⊆ P₀) with hA₀def
  have mem_A₀ {p : ℤ × ℤ} : p ∈ A₀ ↔ p ∈ dil3 A ∧ cell p ⊆ P₀ := by
    classical
    rw [hA₀def]
    exact Finset.mem_filter
  have hA₀eq : cellUnion A₀ = P₀ := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
      exact (mem_A₀.mp hp).2 hzp
    · intro z hz
      have hzP : z ∈ cellUnion (dil3 A) := hP₀sub hz
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hzP
      have hcell : cell p ⊆ P₀ := by
        have h1 : cell p ⊆ connectedComponentIn (cellUnion (dil3 A)) z :=
          (convex_cell p).isPreconnected.subset_connectedComponentIn (x := z) hzp
            (fun w hw => cell_subset_cellUnion hp hw)
        have h2 : connectedComponentIn (cellUnion (dil3 A)) z = P₀ :=
          (connectedComponentIn_eq hz).symm.trans hP₀def.symm
        rwa [h2] at h1
      exact Set.mem_iUnion₂.mpr ⟨p, mem_A₀.mpr ⟨hp, hcell⟩, hzp⟩
  have hA₀ne : A₀.Nonempty := by
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp (ha₁P)
    have hcell : cell p ⊆ P₀ :=
      (convex_cell p).isPreconnected.subset_connectedComponentIn hzp (fun w hw => cell_subset_cellUnion hp hw)
    exact ⟨p, mem_A₀.mpr ⟨hp, hcell⟩⟩
  have ha₁int : a₁ ∈ interior (cellUnion A₀) := by
    rw [hA₀eq]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a₁ (hS₁_int ha₁)
    refine mem_interior_iff_mem_nhds.mpr ?_
    refine Filter.mem_of_superset (Metric.ball_mem_nhds a₁ hε) ?_
    exact (convex_ball a₁ ε).isPreconnected.subset_connectedComponentIn (Metric.mem_ball_self hε)
      (fun w hw => interior_subset (hball hw))
  -- extraction
  obtain ⟨γ₁, hγ₁inj, hγ₁rng, hγ₁a, hγ₁bdd⟩ :=
    exists_jordan_curve_of_cellUnion hA₀ne (hA₀eq ▸ hP₀conn) ha₁int
  -- the frontier of `P₀` avoids `S₁`
  have hS₁_disj : ∀ z ∈ S₁, z ∉ frontier P₀ := by
    intro z hz hzfr
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z (hS₁_int hz)
    obtain ⟨w, hwP₀, hwdist⟩ := Metric.mem_closure_iff.mp hzfr.1 ε hε
    have hwb : w ∈ Metric.ball z ε := by
      rw [Metric.mem_ball]; rwa [dist_comm]
    have hsub : Metric.ball z ε ⊆ P₀ := by
      have h1 : Metric.ball z ε ⊆ connectedComponentIn (cellUnion (dil3 A)) w :=
        (convex_ball z ε).isPreconnected.subset_connectedComponentIn hwb
          (fun u hu => interior_subset (hball hu))
      have h2 : connectedComponentIn (cellUnion (dil3 A)) w = P₀ :=
        (connectedComponentIn_eq hwP₀).symm.trans hP₀def.symm
      rwa [h2] at h1
    exact hzfr.2 (mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.ball_mem_nhds z hε) hsub))
  -- the range of the extracted curve lies in the frontier of `P₀`, hence in `P₀`
  have hγ₁fr : Set.range γ₁ ⊆ frontier P₀ := by
    rw [← hA₀eq]; exact hγ₁rng
  have hγ₁sub : Set.range γ₁ ⊆ P₀ := by
    have h2 : frontier P₀ ⊆ P₀ := by
      calc frontier P₀ ⊆ closure P₀ := frontier_subset_closure
        _ = P₀ := hP₀cl.closure_eq
    exact hγ₁fr.trans h2
  -- the curve avoids `S₁` and `S₁'`
  have hγnotS₁ : ∀ w : Circle, γ₁ w ∉ S₁ := by
    intro w hw
    exact hS₁_disj (γ₁ w) hw (hγ₁fr (Set.mem_range_self w))
  have hγnotS₁' : ∀ w : Circle, γ₁ w ∉ S₁' := by
    intro w hw
    have hmem : γ₁ w ∈ cellUnion (dil3 A) := hP₀sub (hγ₁sub (Set.mem_range_self w))
    have hbdd : Metric.infDist (γ₁ w) S₁ ≤ 2 * Real.sqrt 2 :=
      dist_le_of_mem_cellUnion_dil3 hA_spec hmem
    have hle : δ / h ≤ Metric.infDist (γ₁ w) S₁ :=
      (Metric.le_infDist hS₁ne).mpr (fun y hy => by
        rw [dist_comm]; exact hgap₁ y hy (γ₁ w) hw)
    exact absurd (lt_of_le_of_lt hle (lt_of_le_of_lt hbdd hhgap)) (lt_irrefl _)
  -- unscale
  have hkey : ∀ z : ℂ, c * (((h : ℝ) : ℂ) * z) = z := by
    intro z
    rw [← mul_assoc, hcinv, one_mul]
  have hhne : ((h : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hhpos
  refine ⟨⟨fun w : Circle => ((h : ℝ) : ℂ) * γ₁ w, by fun_prop⟩, ?_, ?_, ?_, ?_⟩
  · rintro w w' hww
    exact hγ₁inj (mul_left_cancel₀ hhne hww)
  · rintro z ⟨w, hwz⟩
    rw [← hwz]
    intro hz
    rcases hz with hz | hz
    · exact hγnotS₁ w (by
        have h1 : c * (((h : ℝ) : ℂ) * γ₁ w) ∈ S₁ := ⟨((h : ℝ) : ℂ) * γ₁ w, hz, rfl⟩
        rwa [hkey] at h1)
    · exact hγnotS₁' w (by
        have h1 : c * (((h : ℝ) : ℂ) * γ₁ w) ∈ S₁' := ⟨((h : ℝ) : ℂ) * γ₁ w, hz, rfl⟩
        rwa [hkey] at h1)
  · intro hcon
    obtain ⟨w, hw⟩ := hcon
    have h1 : c * a = γ₁ w := by
      have h2 : c * a = c * (((h : ℝ) : ℂ) * γ₁ w) := congrArg (fun t => c * t) hw.symm
      rw [h2, ← mul_assoc, hcinv, one_mul]
    have h2 : a₁ = γ₁ w := by
      rw [ha₁def]
      exact h1
    exact hγ₁a ⟨w, h2.symm⟩
  · have hbdd2 := isBounded_connectedComponentIn_mul (c := h) hhpos hγ₁bdd
    have himg : (fun z : ℂ => ((h : ℝ) : ℂ) * z) '' Set.range γ₁
        = Set.range (fun w : Circle => ((h : ℝ) : ℂ) * γ₁ w) :=
      (Set.range_comp (fun z : ℂ => ((h : ℝ) : ℂ) * z) γ₁).symm
    have haeq : ((h : ℝ) : ℂ) * a₁ = a := by
      rw [ha₁def]
      calc ((h : ℝ) : ℂ) * (c * a) = (((h : ℝ) : ℂ) * c) * a := by rw [mul_assoc]
        _ = 1 * a := by rw [mul_comm ((h : ℝ) : ℂ) c, hcinv]
        _ = a := one_mul a
    rwa [himg, haeq] at hbdd2

end Work.HornSC
