import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Engulf.E4alt.Gp
import Submission.Work.Engulf.E4alt.Helpers
import Submission.Work.Engulf.Auxi.exists_subdiv_affine
import Submission.Work.Engulf.Auxi.locally_affine_of_convex
import Submission.Work.Engulf.Auxi.vertexPerturbForm
import Submission.Work.Engulf.Auxi.EngulfAux
import Submission.Work.Engulf.E4Aux.tietze
import Submission.Work.Engulf.E4Aux.prep
import Submission.Work.Engulf.E4Aux.continuousOn_ite_of_closure
import Submission.Work.Engulf.E4Aux.injOn_of_affineIndependent_image
import Submission.Work.Engulf.Vpf.Defs
import Submission.Work.Engulf.Vpf.vpfApplyNotMem
import Submission.Work.Geo.Radial.ChartImage
import Submission.Work.Geo.Radial.continuousOn_chartInv
import Submission.Work.PL.Generic.gp_pairs_pairwise
import Submission.Work.PL.Generic.gp_pairs_fixed
import Submission.Work.PL.Generic.affineIndependent_of_gp
import Submission.Work.Cells.Connell.meshLT_dist_lt

set_option maxHeartbeats 1000000

namespace Work.Engulf.E4alt

open Set Metric
open _root_.PL
open scoped Topology

/-! ## Elementary helpers -/

/-- Thickenings of the chart image of a closed cube. -/
theorem exists_thickening_chart_openCube {n : ℕ} {M : Type*} [MetricSpace M]
    (ψ : CubeChart n M) {r r' : ℝ} (hrr' : r < r') (hr'1 : r' < 1) :
    ∃ ρ > 0, ∀ y ∈ ψ.toFun '' closedCube r, ∀ z : M, dist z y < ρ →
      z ∈ ψ.toFun '' openCube r' := by
  have hK : IsCompact (ψ.toFun '' closedCube r) :=
    Work.Geo.Radial.isCompact_image_closedCube ψ r (lt_of_lt_of_le hrr' hr'1.le)
  have hO : IsOpen (ψ.toFun '' openCube r') :=
    Work.Geo.Radial.isOpen_image_of_subset ψ (isOpen_openCube r')
      (openCube_mono (le_of_lt hr'1))
  have hsub : ψ.toFun '' closedCube r ⊆ ψ.toFun '' openCube r' :=
    Set.image_mono (closedCube_subset_openCube hrr')
  obtain ⟨ρ, hρ, hρsub⟩ := hK.exists_thickening_subset_open hO hsub
  exact ⟨ρ, hρ, fun y hy z hz => hρsub (Metric.mem_thickening_iff.mpr ⟨y, hy, hz⟩)⟩

/-- Thickenings of the chart image of a closed cube, with a closed target. -/
theorem exists_thickening_chart_closedCube {n : ℕ} {M : Type*} [MetricSpace M]
    (ψ : CubeChart n M) {r r' : ℝ} (hrr' : r < r') (hr'1 : r' < 1) :
    ∃ ρ > 0, ∀ y ∈ ψ.toFun '' closedCube r, ∀ z : M, dist z y < ρ →
      z ∈ ψ.toFun '' closedCube r' := by
  obtain ⟨ρ, hρ, h⟩ := exists_thickening_chart_openCube ψ hrr' hr'1
  exact ⟨ρ, hρ, fun y hy z hz =>
    Set.image_mono (openCube_subset_closedCube r') (h y hy z hz)⟩

/-- `chartInv` of a point of `ψ '' closedCube r` lies in `closedCube r`. -/
theorem chartInv_mem_closedCube {n : ℕ} {M : Type*} [TopologicalSpace M] (ψ : CubeChart n M)
    {r : ℝ} (hr : r < 1) {p : M} (hp : p ∈ ψ.toFun '' closedCube r) :
    Work.Geo.Radial.chartInv ψ p ∈ closedCube r := by
  obtain ⟨y, hy, hyψ⟩ := hp
  rw [← hyψ, Work.Geo.Radial.chartInv_apply ψ (closedCube_subset_openCube hr hy)]
  exact hy

/-- For `n ≥ 1` a cube chart does not map the whole open cube onto a smaller open cube's image. -/
theorem exists_notMem_chartImage_openCube {n : ℕ} {M : Type*} [MetricSpace M]
    (ψ : CubeChart n M) (hn : 1 ≤ n) {r r' : ℝ} (hr : 0 < r) (hrr' : r < r') (hr'1 : r' < 1) :
    ∃ p : M, p ∉ ψ.toFun '' openCube (r : ℝ) := by
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set y : PL.E n := (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i => if i = i0 then (r' + 1) / 2 else 0) with hy
  have key : ∀ i, y i = (if i = i0 then (r' + 1) / 2 else 0) := by
    intro i; rw [hy]; simp
  have hy_open : y ∈ openCube (n := n) 1 := by
    intro i
    rw [key i]
    by_cases h : i = i0
    · subst h; rw [ite_eq_left rfl, abs_lt]; constructor <;> linarith
    · rw [ite_eq_right h, abs_zero]; linarith
  refine ⟨ψ.toFun y, fun hcon => ?_⟩
  obtain ⟨z, hz, hzψ⟩ := hcon
  have hz1 : z ∈ openCube (n := n) 1 := openCube_mono (le_of_lt (lt_trans hrr' hr'1)) hz
  have heq : y = z := Work.Geo.Radial.toFun_injOn_openCube ψ hy_open hz1 (by rw [hzψ])
  have hzi : |z i0| < r := hz i0
  rw [← heq, key i0, ite_eq_left rfl] at hzi
  rw [abs_of_pos (by linarith : (0:ℝ) < (r' + 1) / 2)] at hzi
  linarith

/-- The subtype version of a finite set of vertices. -/
def subV {N : ℕ} (Vt : Finset (PL.E N)) (σ : Finset (PL.E N)) (hV : ∀ v ∈ σ, v ∈ Vt) :
    Finset ↥Vt :=
  σ.attach.map ⟨fun v => (⟨v.1, hV v.1 v.2⟩ : ↥Vt), fun a b hab =>
      Subtype.ext (by
        have h1 : ((fun v : ↥σ => (⟨v.1, hV v.1 v.2⟩ : ↥Vt)) a).1
            = ((fun v : ↥σ => (⟨v.1, hV v.1 v.2⟩ : ↥Vt)) b).1 :=
          congrArg Subtype.val hab
        simpa using h1)⟩

theorem mem_subV {N : ℕ} {Vt : Finset (PL.E N)} {σ : Finset (PL.E N)}
    (hV : ∀ v ∈ σ, v ∈ Vt) (w : ↥Vt) : w ∈ subV Vt σ hV ↔ w.1 ∈ σ := by
  rw [subV, Finset.mem_map]
  constructor
  · rintro ⟨v, -, hvw⟩
    rw [← hvw]; exact v.2
  · intro hw
    exact ⟨⟨w.1, hw⟩, Finset.mem_attach σ ⟨w.1, hw⟩, Subtype.ext rfl⟩

/-- The lift of a function on the vertices, as an image of a finite set. -/
theorem image_lift_eq {N n : ℕ} (Vt : Finset (PL.E N)) (yy : ↥Vt → PL.E n)
    (T : Finset (PL.E N)) (hT : ∀ v ∈ T, v ∈ Vt) :
    (fun v => if hv : v ∈ Vt then yy ⟨v, hv⟩ else 0) '' (T : Set (PL.E N))
      = yy '' ((subV Vt T hT : Finset ↥Vt) : Set ↥Vt) := by
  rw [subV]
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp only [dif_pos (hT v hv)]
    exact ⟨⟨v, hT v hv⟩,
      Finset.mem_map.mpr ⟨⟨v, hv⟩, Finset.mem_attach T ⟨v, hv⟩, rfl⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_map] at hw
    obtain ⟨v, -, rfl⟩ := hw
    refine ⟨v.1, v.2, ?_⟩
    simp only [dif_pos (hT v.1 v.2)]
    exact congrArg yy (Subtype.ext rfl)

/-- Generic position implies affine independence (variant with the hypothesis restricted to the
finite vertex set `Vt`). -/
theorem affineIndependent_of_gp_Vt {n : ℕ} {N : ℕ} {Vt : Finset (PL.E N)} (fz : Finset (PL.E N))
    (y : PL.E N → PL.E n) (σ : Finset (PL.E N)) (hσVt : ∀ v ∈ σ, v ∈ Vt)
    (hcard : σ.card ≤ n + 1)
    (hgp : ∀ u ∈ Vt, u ∉ fz → ∀ T : Finset (PL.E N), T ⊆ σ → u ∉ T →
      y u ∈ (affineSpan ℝ (y '' (T : Set (PL.E N))) : Set (PL.E n)) →
        affineSpan ℝ (y '' (T : Set (PL.E N))) = ⊤)
    (hnd : AffineIndependent ℝ (fun v : ↥(σ ∩ fz) => y v)) :
    AffineIndependent ℝ (fun v : ↥σ => y v) := by
  classical
  by_contra hcon
  obtain ⟨c, hc0, hcy, v0, hv0, hcv0⟩ :=
    Work.PL.Generic.exists_coeff_of_not_affineIndependent y σ hcon
  have hex : ∃ u, u ∈ σ ∧ c u ≠ 0 ∧ u ∉ fz := by
    by_contra h
    push_neg at h
    exact hcv0 (Work.PL.Generic.eq_zero_of_dependence_supported_on_frozen fz y σ hnd hc0 hcy
      (fun v hv hcv => h v hv (fun hvz => hcv hvz)) v0 hv0)
  obtain ⟨u, huσ, hcu, hufz⟩ := hex
  have hmem : y u ∈ (affineSpan ℝ (y '' ((σ.erase u : Finset (PL.E N)) : Set (PL.E N))) :
      Set (PL.E n)) :=
    Work.PL.Generic.mem_affineSpan_erase_of_sum_smul_eq_zero σ y huσ hcu hc0 hcy
  have htop := hgp u (hσVt u huσ) hufz (σ.erase u) (Finset.erase_subset u σ)
    (Finset.notMem_erase u σ) hmem
  have hcard' : (σ.erase u).card ≤ n := by rw [Finset.card_erase_of_mem huσ]; omega
  exact Work.PL.Generic.affineSpan_image_ne_top_of_card_le y (σ.erase u) hcard' htop

/-- Affine independence transfers along a reindexing. -/
theorem affineIndependent_comp_equiv {n : ℕ} {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (p : β → PL.E n) (q : α → PL.E n) (h : ∀ i, p (e i) = q i)
    (hp : AffineIndependent ℝ q) : AffineIndependent ℝ p := by
  rw [affineIndependent_iff] at hp ⊢
  intro s w hw0 hwy u hu
  have h0 : ∑ i ∈ s.image e.symm, w (e i) = 0 := by
    rw [Finset.sum_image]
    · simpa using hw0
    · intro a _ b _ hab; exact e.symm.injective hab
  have hy : ∑ i ∈ s.image e.symm, w (e i) • q i = 0 := by
    rw [Finset.sum_image]
    · refine (Finset.sum_congr rfl fun i hi => ?_).trans hwy
      have hq : q (e.symm i) = p i := by
        have h1 := h (e.symm i)
        rw [Equiv.apply_symm_apply] at h1
        exact h1.symm
      rw [Equiv.apply_symm_apply, hq]
    · intro a _ b _ hab; exact e.symm.injective hab
  have hres := hp (s.image e.symm) (fun i => w (e i)) h0 hy (e.symm u)
    (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  simpa using hres

theorem exists_normData (n p q : ℕ) (T : Work.Engulf.ToolsAll n) (hq : q + 1 ≤ p + 1)
    {M : Type*} [MetricSpace M] {V X : Set M} {N : ℕ} {Γ : PL.Cx N} {K L : Set (PL.E N)}
    {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    (A : Work.Engulf.Amb n p M V) (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (SCh : Work.Engulf.SmoothChart p X Γ L f ψ)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε,
      Work.Engulf.Alt.Core11 ND ∧ Work.Engulf.Alt.CarrierS ND := by
  classical
  -- ===== 0. hypotheses =====
  have hΓfin : Γ.faces.Finite := H7.cfg.fin
  have hcont : ContinuousOn f Γ.space := H7.cfg.cont
  have hsubL : IsSubSp Γ L := H7.cfg.subL
  have hΔmem : τ₀ ∪ τ₁ ∈ Γ.faces := H7.mem
  have hτ₁ss : τ₁ ⊂ τ₀ ∪ τ₁ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right, ?_⟩
    intro hEq
    obtain ⟨u, hu⟩ := H7.ne₀
    have hu₁ : u ∈ τ₁ := by rw [hEq]; exact Finset.mem_union_left τ₁ hu
    exact (Finset.disjoint_left.mp H7.disj hu) hu₁
  -- ===== 1. margins =====
  obtain ⟨ρo, hρo_pos, hρo⟩ :=
    exists_thickening_chart_openCube ψ (r := 11/16) (r' := 3/4) (by norm_num) (by norm_num)
  obtain ⟨ρf, hρf_pos, hρf⟩ :=
    exists_thickening_chart_closedCube ψ (r := 9/16) (r' := 5/8) (by norm_num) (by norm_num)
  obtain ⟨ρh, hρh_pos, hρh⟩ :=
    exists_thickening_chart_closedCube ψ (r := 1/2) (r' := 5/8) (by norm_num) (by norm_num)
  have hKc : IsCompact K := Work.Engulf.isCompact_of_isSubSp hΓfin H7.subK
  have hfKc : IsCompact (f '' K) :=
    hKc.image_of_continuousOn (hcont.mono H7.subK.subset_space)
  obtain ⟨δV, hδV_pos, hδV⟩ :=
    hfKc.exists_thickening_subset_open A.Vo (fun y hy => H7.engK (Or.inr hy))
  -- ===== 2. the budget =====
  set m0 : ℝ := min (ε / 2) (min (1 / 32) (min ρo (min (ρf / 2) (min (ρh / 2) (δV / 2)))))
    with hm0def
  have hm0pos : 0 < m0 := by
    rw [hm0def]
    exact lt_min (by linarith) (lt_min (by norm_num) (lt_min hρo_pos (lt_min (by positivity)
      (lt_min (by positivity) (by positivity)))))
  have hm0ε : m0 ≤ ε / 2 := by rw [hm0def]; exact min_le_left _ _
  have hm032 : m0 ≤ 1 / 32 := by
    rw [hm0def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hm0ρo : m0 ≤ ρo := by
    rw [hm0def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm0ρf : m0 ≤ ρf / 2 := by
    rw [hm0def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hm0ρh : m0 ≤ ρh / 2 := by
    rw [hm0def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hm0δV : m0 ≤ δV / 2 := by
    rw [hm0def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  set η : ℝ := m0 / 4 with hηdef
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hη16 : η ≤ 1 / 16 := by rw [hηdef]; linarith [hm032, hm0pos]
  have hηε : η < ε := by rw [hηdef]; linarith [hm0ε, hε, hm0pos]
  have hηρf : η ≤ ρf / 2 := by rw [hηdef]; linarith [hm0ρf, hρf_pos]
  have hηρh : η ≤ ρh / 2 := by rw [hηdef]; linarith [hm0ρh, hρh_pos]
  have hηδV : η ≤ δV / 2 := by rw [hηdef]; linarith [hm0δV, hδV_pos]
  -- uniform continuity of the chart on the cube
  have hucψ : UniformContinuousOn ψ.toFun (closedCube (n := n) (13/16 : ℝ)) :=
    (isCompact_closedCube (13/16 : ℝ)).uniformContinuousOn_of_continuous
      (ψ.cont.mono (closedCube_subset_openCube (by norm_num : (13/16:ℝ) < 1)))
  obtain ⟨θ, hθ_pos, hθ⟩ := Metric.uniformContinuousOn_iff.mp hucψ (η / 2) (by linarith)
  set εpl : ℝ := min (m0 / 64) (θ / 8) with hεpldef
  have hεpl0 : 0 < εpl := by rw [hεpldef]; exact lt_min (by positivity) (by positivity)
  have hεplm0 : εpl ≤ m0 / 64 := by rw [hεpldef]; exact min_le_left _ _
  have hεplθ : εpl ≤ θ / 8 := by rw [hεpldef]; exact min_le_right _ _
  have hεpl16 : εpl < 1 / 16 := by linarith [hεplm0, hm032, hm0pos]
  have hεplρo : εpl < ρo / 2 := by linarith [hεplm0, hm0ρo, hρo_pos, hm0pos]
  set εgp : ℝ := min (m0 / 64) (θ / 8) with hεgpdef
  have hεgp0 : 0 < εgp := by rw [hεgpdef]; exact lt_min (by positivity) (by positivity)
  have hεgpm0 : εgp ≤ m0 / 64 := by rw [hεgpdef]; exact min_le_left _ _
  have hεgpθ : εgp ≤ θ / 8 := by rw [hεgpdef]; exact min_le_right _ _
  have hεsumθ : εpl + εgp < θ := by linarith [hεplθ, hεgpθ, hθ_pos]
  have hεsumsmall : εpl + εgp ≤ 1 / 1024 := by
    linarith [hεplm0, hεgpm0, hm032, hm0pos]
  -- ===== 3. the chart-coordinate approximation `f_c` =====
  set Cf : Set (PL.E N) := Γ.space ∩ f ⁻¹' (ψ.toFun '' closedCube (3/4 : ℝ)) with hCfdef
  have hCf_cl : IsClosed Cf := by
    rw [hCfdef]
    exact ContinuousOn.preimage_isClosed_of_isClosed hcont (isClosed_space hΓfin)
      (Work.Geo.Radial.isCompact_image_closedCube ψ (3/4) (by norm_num)).isClosed
  have hchartInv_cont : ContinuousOn (fun x => Work.Geo.Radial.chartInv ψ (f x)) Cf := by
    rw [hCfdef]
    refine (Work.Geo.Radial.continuousOn_chartInv ψ).comp (hcont.mono Set.inter_subset_left) ?_
    rintro x ⟨-, y, hy, hyψ⟩
    exact ⟨y, closedCube_subset_openCube (by norm_num : (3/4:ℝ) < 1) hy, hyψ⟩
  obtain ⟨fc0, hfc0cont, hfc0eq⟩ := Work.Engulf.E4Aux.tietze hCf_cl hchartInv_cont
  set f_c : PL.E N → PL.E n := fun x => Work.Engulf.E4Aux.clampCube (3/4) (fc0 x) with hfcdef
  have hfceq : ∀ x, f_c x = Work.Engulf.E4Aux.clampCube (3/4) (fc0 x) := fun x => rfl
  have hfc_cont : Continuous f_c :=
    (Work.Engulf.E4Aux.continuous_clampCube (n := n) (3/4)).comp hfc0cont
  have hfc_mem : ∀ x, f_c x ∈ closedCube (3/4 : ℝ) := fun x => by
    rw [hfceq]; exact Work.Engulf.E4Aux.clampCube_mem (n := n) (by norm_num) (fc0 x)
  have hfc_C : Set.EqOn f_c (fun x => Work.Geo.Radial.chartInv ψ (f x)) Cf := by
    intro x hx
    rw [hfceq, hfc0eq hx]
    obtain ⟨-, y, hy, hyψ⟩ := hx
    exact Work.Engulf.E4Aux.clampCube_eq_self (by norm_num) (chartInv_mem_closedCube ψ
      (by norm_num : (3/4:ℝ) < 1) ⟨y, hy, hyψ⟩)
  -- ===== 4. the fine subdivision and the shelling =====
  set δosc : ℝ := min εpl (min (1 / 768) (min ρo (ρf / 2))) with hδoscdef
  have hδosc0 : 0 < δosc := by
    rw [hδoscdef]
    exact lt_min hεpl0 (lt_min (by norm_num) (lt_min hρo_pos (by positivity)))
  have hδosc_εpl : δosc ≤ εpl := by rw [hδoscdef]; exact min_le_left _ _
  have hδosc_768 : δosc ≤ 1 / 768 := by
    rw [hδoscdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδosc_ρo : δosc ≤ ρo := by
    rw [hδoscdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδosc_ρf : δosc ≤ ρf / 2 := by
    rw [hδoscdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨δu1, hδu1_pos, hδu1⟩ := Work.Engulf.exists_mesh_dist_lt (K := Γ) hΓfin hcont hδosc0
  obtain ⟨δu2, hδu2_pos, hδu2⟩ := Work.Engulf.exists_mesh_dist_lt (K := Γ) hΓfin
    hfc_cont.continuousOn hδosc0
  set δu : ℝ := min δu1 δu2 with hδudef
  have hδu_pos : 0 < δu := by rw [hδudef]; exact lt_min hδu1_pos hδu2_pos
  have hδu_f : ∀ x ∈ Γ.space, ∀ y ∈ Γ.space, dist x y < δu → dist (f x) (f y) < δosc :=
    fun x hx y hy h => hδu1 x hx y hy (lt_of_lt_of_le h (by rw [hδudef]; exact min_le_left _ _))
  have hδu_fc : ∀ x ∈ Γ.space, ∀ y ∈ Γ.space, dist x y < δu → dist (f_c x) (f_c y) < δosc :=
    fun x hx y hy h => hδu2 x hx y hy (lt_of_lt_of_le h (by rw [hδudef]; exact min_le_right _ _))
  -- whole-face affinity of `f` on the frozen faces (from the smooth chart)
  obtain ⟨r0, hr0⟩ := Work.Engulf.Aux.exists_subdiv_affine (T N).subdiv ψ hΓfin hsubL hcont SCh
    (fun r s' hs' hs'L => (T N).carrier r Γ hΓfin L hsubL s' hs' hs'L) (β := 23/32)
    (by norm_num) (by norm_num)
  obtain ⟨Rpl, hRpl⟩ := (T N).subdiv.fine Γ hΓfin δu hδu_pos
  set R : ℕ := max (max Rpl r0) 1 with hRdef
  have hRr0 : r0 ≤ R := le_trans (le_max_right Rpl r0) (le_max_left _ _)
  have hRRpl : Rpl ≤ R := le_trans (le_max_left Rpl r0) (le_max_left _ _)
  have hR1 : 1 ≤ R := le_max_right _ _
  set Γ₁ : PL.Cx N := (T N).subdiv.sdIter R Γ hΓfin with hΓ₁def
  have hΓ₁fin : Γ₁.faces.Finite := (T N).subdiv.fin R Γ hΓfin
  have hsub₁ : Subdivides Γ₁ Γ := (T N).subdiv.subdiv R Γ hΓfin
  have hspace₁ : Γ₁.space = Γ.space := hsub₁.1
  have hmesh₁ : MeshLT Γ₁ δu := hRpl R hRRpl
  have hsubL₁ : IsSubSp Γ₁ L := (T N).subdiv.subsp R Γ hΓfin L hsubL
  obtain ⟨ord, hord_nodup, hord_mem, hord_cov, hord_split⟩ :=
    (T N).subdiv.shell R Γ hΓfin (τ₀ ∪ τ₁) τ₁ hΔmem H7.ne₁ hτ₁ss
  have hord_mem₁ : ∀ t ∈ ord, t ∈ Γ₁.faces := fun t ht => (hord_mem t ht).1
  have hord_card : ∀ t ∈ ord, t.card = (τ₀ ∪ τ₁).card := fun t ht => (hord_mem t ht).2.1
  have hord_sub : ∀ t ∈ ord, PL.simp t ⊆ PL.simp (τ₀ ∪ τ₁) := fun t ht => (hord_mem t ht).2.2
  have hord_cov₁ : PL.simp (τ₀ ∪ τ₁) ⊆ ⋃ t ∈ ord, PL.simp t := hord_cov.ge
  have hosc_f : ∀ s ∈ Γ₁.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s, dist (f x) (f y) < δosc := by
    intro s hs x hx y hy
    exact hδu_f x (hspace₁ ▸ Geometry.SimplicialComplex.convexHull_subset_space hs hx)
      y (hspace₁ ▸ Geometry.SimplicialComplex.convexHull_subset_space hs hy)
      (Work.Cells.Connell.meshLT_dist_lt hmesh₁ hs hx hy)
  -- ===== 5. the frozen subcomplex `Lt` and the PL approximation `gc` =====
  set Lf : Finset (Finset (PL.E N)) := hΓ₁fin.toFinset.filter
    (fun s => PL.simp s ⊆ L ∧ f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (3/4 : ℝ)) with hLfdef
  set Lt : Set (PL.E N) := ⋃ s ∈ Lf, PL.simp s with hLtdef
  have hLf_faces : ∀ s ∈ Lf, s ∈ Γ₁.faces := fun s hs =>
    (Set.Finite.mem_toFinset hΓ₁fin).mp (Finset.mem_filter.mp hs).1
  have hLf_L : ∀ s ∈ Lf, PL.simp s ⊆ L := fun s hs => (Finset.mem_filter.mp hs).2.1
  have hLf_im : ∀ s ∈ Lf, f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (3/4 : ℝ) :=
    fun s hs => (Finset.mem_filter.mp hs).2.2
  have hLt_sub_L : Lt ⊆ L := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    exact hLf_L s hs hxs
  have hLt_image : f '' Lt ⊆ ψ.toFun '' PL.closedCube (3/4 : ℝ) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    exact hLf_im s hs ⟨x, hxs, rfl⟩
  have hLt_chartImage : ∀ x ∈ Lt, f x ∈ Work.Geo.Radial.chartImage ψ := fun x hx =>
    Set.image_mono (closedCube_subset_openCube (by norm_num : (3/4:ℝ) < 1))
      (hLt_image ⟨x, hx, rfl⟩)
  have hLt_isSubSp : IsSubSp Γ₁ Lt := by
    constructor
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
      exact Geometry.SimplicialComplex.convexHull_subset_space (hLf_faces s hs) hxs
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨s, hLf_faces s hs, hxs, fun y hy => Set.mem_iUnion₂.mpr ⟨s, hs, hy⟩⟩
  have hLt_sub_Cf : Lt ⊆ Cf := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨hspace₁ ▸ Geometry.SimplicialComplex.convexHull_subset_space (hLf_faces s hs) hxs,
      hLt_image ⟨x, hx, rfl⟩⟩
  have hfc_Lt : ∀ x ∈ Lt, f_c x = Work.Geo.Radial.chartInv ψ (f x) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    have hxCf : x ∈ Cf := hLt_sub_Cf hx
    rw [hfceq, hfc0eq hxCf]
    exact Work.Engulf.E4Aux.clampCube_eq_self (by norm_num)
      (chartInv_mem_closedCube ψ (by norm_num : (3/4:ℝ) < 1) (hLf_im s hs ⟨x, hxs, rfl⟩))
  have hmem_Lt : ∀ x ∈ L, f x ∈ ψ.toFun '' PL.openCube (11/16 : ℝ) → x ∈ Lt := by
    intro x hxL hfx
    obtain ⟨t, htΓ₁, hxt, htL⟩ := hsubL₁.2 x hxL
    refine Set.mem_iUnion₂.mpr ⟨t, ?_, hxt⟩
    refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset hΓ₁fin).mpr htΓ₁, htL, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    refine Set.image_mono (openCube_subset_closedCube (3/4)) (hρo (f x)
      (Set.image_mono (openCube_subset_closedCube (11/16)) hfx) (f z) ?_)
    exact lt_of_lt_of_le
      (hδu_f z (hspace₁ ▸ Geometry.SimplicialComplex.convexHull_subset_space htΓ₁ hz)
        x (hspace₁ ▸ Geometry.SimplicialComplex.convexHull_subset_space htΓ₁ hxt)
        (Work.Cells.Connell.meshLT_dist_lt hmesh₁ htΓ₁ hz hxt)) hδosc_ρo
  have hlinHyp : ∀ s ∈ Γ₁.faces, PL.simp s ⊆ Lt →
      (∃ x ∈ PL.simp s, f_c x ∈ closedCube (23/32 : ℝ)) →
      ∃ M' : PL.E N →ᵃ[ℝ] PL.E n, EqOn f_c M' (PL.simp s) := by
    intro s hs hsLt htrig
    obtain ⟨x, hxs, hxβ⟩ := htrig
    have hxLt : x ∈ Lt := hsLt hxs
    have hxβ' : f x ∈ ψ.toFun '' closedCube (23/32 : ℝ) := by
      have h1 : f_c x = Work.Geo.Radial.chartInv ψ (f x) := hfc_Lt x hxLt
      rw [h1] at hxβ
      exact ⟨Work.Geo.Radial.chartInv ψ (f x), hxβ,
        Work.Geo.Radial.chartInv_toFun ψ (hLt_chartImage x hxLt)⟩
    have hims : f '' PL.simp s ⊆ ψ.toFun '' closedCube (3/4 : ℝ) := by
      rintro _ ⟨z, hz, rfl⟩
      exact hLt_image ⟨z, hsLt hz, rfl⟩
    obtain ⟨A', hA'⟩ := hr0 R hRr0 s hs (hsLt.trans hLt_sub_L) hims ⟨x, hxs, hxβ'⟩
    refine ⟨A', fun y hy => ?_⟩
    rw [hfc_Lt y (hsLt hy), (hA' y hy).2,
      Work.Geo.Radial.chartInv_apply ψ (hA' y hy).1]
  have hosc_c : ∀ s ∈ Γ₁.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s,
      dist (f_c x) (f_c y) < min εpl (((23/32 : ℝ) - 11/16) / 24) := by
    intro s hs x hx y hy
    have hxy : dist x y < δu := Work.Cells.Connell.meshLT_dist_lt hmesh₁ hs hx hy
    have hxΓ : x ∈ Γ.space := hspace₁ ▸ Geometry.SimplicialComplex.convexHull_subset_space hs hx
    have hyΓ : y ∈ Γ.space := hspace₁ ▸ Geometry.SimplicialComplex.convexHull_subset_space hs hy
    have hβmα : ((23:ℝ)/32 - 11/16)/24 = 1/768 := by norm_num
    rw [hβmα]
    exact lt_of_lt_of_le (hδu_fc x hxΓ y hyΓ hxy) (le_min hδosc_εpl hδosc_768)
  obtain ⟨gc, hgc_cont, hgc_near, hgc_frz, hgc_off, hgc_aff⟩ :=
    (T N).plApproxAt Γ hΓfin R Lt hLt_isSubSp f_c hfc_cont.continuousOn (11/16) (23/32)
      (by norm_num) (by norm_num) (by norm_num) εpl hεpl0 hlinHyp hosc_c
  -- ===== 6. the vertex set, the perturbation data =====
  set Vt : Finset (PL.E N) := hΓ₁fin.toFinset.biUnion id with hVtdef
  have hVt_mem : ∀ v, v ∈ Vt ↔ ∃ s ∈ Γ₁.faces, v ∈ s := by
    intro v
    rw [hVtdef, Finset.mem_biUnion]
    constructor
    · rintro ⟨s, hs, hvs⟩
      exact ⟨s, (Set.Finite.mem_toFinset hΓ₁fin).mp hs, hvs⟩
    · rintro ⟨s, hs, hvs⟩
      exact ⟨s, (Set.Finite.mem_toFinset hΓ₁fin).mpr hs, hvs⟩
  have hfc_core : ∀ x ∈ Γ.space, f x ∈ ψ.toFun '' closedCube (5/8 : ℝ) →
      f_c x ∈ closedCube (5/8 : ℝ) := by
    intro x hxΓ hx
    rw [hfc_C ⟨hxΓ, Set.image_mono (closedCube_mono (by norm_num : (5/8:ℝ) ≤ 3/4)) hx⟩]
    exact chartInv_mem_closedCube ψ (by norm_num : (5/8:ℝ) < 1) hx
  have hgc_core : ∀ v ∈ Vt, f v ∈ ψ.toFun '' closedCube (5/8 : ℝ) →
      gc v ∈ closedCube (11/16 : ℝ) := by
    intro v hv hvcore
    have hvΓ : v ∈ Γ₁.space := by
      obtain ⟨s, hs, hvs⟩ := (hVt_mem v).mp hv
      exact Geometry.SimplicialComplex.convexHull_subset_space hs (subset_simp hvs)
    have hvΓ' : v ∈ Γ.space := hspace₁ ▸ hvΓ
    have hnear : dist (gc v) (f_c v) < εpl := hgc_near v hvΓ'
    have hfcv : f_c v ∈ closedCube (5/8 : ℝ) := hfc_core v hvΓ' hvcore
    intro i
    have hcoord : |gc v i - f_c v i| ≤ dist (gc v) (f_c v) := by
      rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (gc v - f_c v) i
    have h1' := abs_le.mp (le_of_lt (lt_of_le_of_lt hcoord hnear))
    have h2' := abs_le.mp (hfcv i)
    rw [abs_le]
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2, hεpl16, hεpl0]
  have hgc_cl : ∀ x ∈ Γ₁.space, gc x ∈ closedCube (13/16 : ℝ) := by
    intro x hx i
    have h2 : dist (gc x) (f_c x) < εpl := hgc_near x (hspace₁ ▸ hx)
    have h1 : |gc x i - f_c x i| ≤ dist (gc x) (f_c x) := by
      rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (gc x - f_c x) i
    have h3 : |f_c x i| ≤ 3/4 := hfc_mem x i
    rw [abs_le] at h1 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2, h2, hεpl16, hεpl0]
  set Z : Finset (PL.E N) := Vt.filter (fun v => v ∉ L ∧ f v ∈ ψ.toFun '' closedCube (5/8 : ℝ))
    with hZdef
  set Fzv : Finset (PL.E N) := Vt.filter (fun v => v ∈ L ∨ f v ∉ ψ.toFun '' closedCube (5/8 : ℝ))
    with hFzvdef
  have hZmem : ∀ v, v ∈ Z ↔ v ∈ Vt ∧ v ∉ L ∧ f v ∈ ψ.toFun '' closedCube (5/8 : ℝ) := by
    intro v; rw [hZdef, Finset.mem_filter]
  have hFzmem : ∀ v, v ∈ Fzv ↔ v ∈ Vt ∧ (v ∈ L ∨ f v ∉ ψ.toFun '' closedCube (5/8 : ℝ)) := by
    intro v; rw [hFzvdef, Finset.mem_filter]
  have hZ_sub : Z ⊆ Vt := Finset.filter_subset _ _
  have hFzv_sub : Fzv ⊆ Vt := Finset.filter_subset _ _
  have hZnotFz : ∀ v ∈ Vt, (v ∈ Z ↔ v ∉ Fzv) := by
    intro v hv
    rw [hZmem v, hFzmem v]
    constructor
    · rintro ⟨-, hvL, hvc⟩ ⟨-, hL | hnc⟩
      · exact hvL hL
      · exact hnc hvc
    · intro h
      exact ⟨hv, (fun hL => h ⟨hv, Or.inl hL⟩), (by by_contra hnc; exact h ⟨hv, Or.inr hnc⟩)⟩
  have hZaff : ∀ s ∈ Γ₁.faces, (∃ v ∈ s, v ∈ Z) →
      ∃ M' : PL.E N →ᵃ[ℝ] PL.E n, EqOn gc (⇑M') (PL.simp s) := by
    intro s hs ⟨v, hvs, hvZ⟩
    obtain ⟨hvt, hvL, hvcore⟩ := (hZmem v).mp hvZ
    exact hgc_aff s hs ⟨v, subset_simp hvs, hgc_core v hvt hvcore⟩
  obtain ⟨P, hDomP, hPX⟩ := SCh.1
  obtain ⟨Xcov, hXcov_card', hXcov_sub'⟩ := hDomP
  have hXcov_card : ∀ S ∈ Xcov, S.card ≤ p + 1 := fun S hS => by
    have h := hXcov_card' S hS
    omega
  have hXcov_cov : ∀ y ∈ closedCube (1 : ℝ), ψ.toFun y ∈ X → y ∈ ⋃ S ∈ Xcov, PL.simp S :=
    fun y hy hyX => hXcov_sub' (hPX y hy hyX)
  set fz : Finset (↥Vt) := Vt.attach.filter (fun v => v.val ∈ Fzv) with hfzdef
  have hfz_mem : ∀ (v : ↥Vt), v ∈ fz ↔ v.val ∈ Fzv := by
    intro v; rw [hfzdef, Finset.mem_filter]; simp
  obtain ⟨yy, hyy_dist, hyy_frz, hyy_gp, hyy_gpS⟩ :=
    Work.Engulf.Alt.exists_gp_perturb (n := n) (ι := ↥Vt) fz (fun v => gc v.val) Xcov εgp hεgp0
  set vl : PL.E N → PL.E n := fun v => if hv : v ∈ Vt then yy ⟨v, hv⟩ else 0 with hvldef
  have hvl_eq : ∀ (v : ↥Vt), vl v.val = yy v := by
    intro v; rw [hvldef]; exact dif_pos v.2
  have hvl_dist : ∀ v ∈ Vt, dist (vl v) (gc v) < εgp := fun v hv => by
    rw [hvl_eq ⟨v, hv⟩]; exact hyy_dist ⟨v, hv⟩
  have hvl_frz : ∀ v ∈ Fzv, vl v = gc v := fun v hv => by
    rw [hvl_eq ⟨v, hFzv_sub hv⟩]
    exact hyy_frz ⟨v, hFzv_sub hv⟩ ((hfz_mem ⟨v, hFzv_sub hv⟩).mpr hv)
  have hshell17 : ∀ v ∈ Vt, v ∈ PL.simp (τ₀ ∪ τ₁) → vl v ∈ openCube (17/32 : ℝ) := by
    intro v hv hvΔ i
    have hvΓ : v ∈ Γ.space :=
      Geometry.SimplicialComplex.convexHull_subset_space hΔmem hvΔ
    have hfv : f v ∈ ψ.toFun '' openCube (1/2 : ℝ) := hch ⟨v, hvΔ, rfl⟩
    have hvCf : v ∈ Cf := ⟨hvΓ,
      Set.image_mono (closedCube_mono (by norm_num : (1/2:ℝ) ≤ 3/4))
        (Set.image_mono (openCube_subset_closedCube (1/2)) hfv)⟩
    obtain ⟨y, hy, hyψ⟩ := hfv
    have hfcy : f_c v = y := by
      have h1 : f_c v = Work.Geo.Radial.chartInv ψ (f v) := hfc_C hvCf
      rw [h1, show f v = ψ.toFun y from hyψ.symm]
      exact Work.Geo.Radial.chartInv_apply ψ (openCube_mono (by norm_num : (1/2:ℝ) ≤ 1) hy)
    have h1 : |vl v i - gc v i| ≤ dist (vl v) (gc v) := by
      rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (vl v - gc v) i
    have h2 : |gc v i - f_c v i| ≤ dist (gc v) (f_c v) := by
      rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (gc v - f_c v) i
    have h1' := abs_le.mp (le_of_lt (lt_of_le_of_lt h1 (hvl_dist v hv)))
    have h2' := abs_le.mp (le_of_lt (lt_of_le_of_lt h2 (hgc_near v hvΓ)))
    rw [hfcy] at h2'
    have hy' := abs_le.mp (le_of_lt (hy i))
    rw [abs_lt]
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2, hy'.1, hy'.2, hεsumsmall]
  set Gv : PL.E N → PL.E n := Work.Engulf.Vpf.vpfG' Γ₁ Z gc vl with hGvdef
  have hGveq : ∀ x, Gv x = Work.Engulf.Vpf.vpfG' Γ₁ Z gc vl x := fun x => rfl
  have hGv_cont : ContinuousOn Gv Γ₁.space :=
    Work.Engulf.Aux.continuousOn_vpfG hΓ₁fin (hspace₁ ▸ hgc_cont) hZaff
  have hGv_dist : ∀ x ∈ Γ₁.space, dist (Gv x) (gc x) ≤ εgp := fun x hx =>
    Work.Engulf.Aux.dist_vpfG_le hZaff hεgp0.le (fun v hv => le_of_lt (hvl_dist v (hZ_sub hv))) hx
  have hGv_cl : ∀ x ∈ Γ₁.space, Gv x ∈ closedCube (13/16 : ℝ) := by
    intro x hx i
    have h1 : |Gv x i - gc x i| ≤ dist (Gv x) (gc x) := by
      rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (Gv x - gc x) i
    have h2 : |gc x i - f_c x i| ≤ dist (gc x) (f_c x) := by
      rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (gc x - f_c x) i
    have h3 : dist (gc x) (f_c x) < εpl := hgc_near x (hspace₁ ▸ hx)
    have h4 : |f_c x i| ≤ 3/4 := hfc_mem x i
    have h1' := abs_le.mp (h1.trans (hGv_dist x hx))
    have h2' := abs_le.mp (le_of_lt (h2.trans_lt h3))
    have h4' := abs_le.mp h4
    rw [abs_le]
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2, h4'.1, h4'.2, hεpl0, hεgp0]
  -- ===== 7. the bump and the normalised map `g₁` =====
  obtain ⟨bb, hb_cont, hb_range, hb_one, hb_zero⟩ :=
    Work.Engulf.Alt.exists_bump ψ (ρ := 5/8) (ρ' := 11/16) (by norm_num) (by norm_num)
      (by norm_num)
  have hScl : IsClosed ((ψ.toFun '' openCube (3/4 : ℝ))ᶜ) := by
    rw [isClosed_compl_iff]
    exact Work.Geo.Radial.isOpen_image_of_subset ψ (isOpen_openCube (3/4))
      (openCube_mono (by norm_num : (3/4:ℝ) ≤ 1))
  have hn1 : 1 ≤ n := by have := A.hp; omega
  have hSne : ((ψ.toFun '' openCube (3/4 : ℝ))ᶜ).Nonempty :=
    exists_notMem_chartImage_openCube ψ hn1 (r := 3/4) (r' := 7/8)
      (by norm_num) (by norm_num) (by norm_num)
  have hchi_iff : ∀ x : PL.E N, Metric.infDist (f x) ((ψ.toFun '' openCube (3/4 : ℝ))ᶜ) = 0 ↔
      f x ∉ ψ.toFun '' openCube (3/4 : ℝ) :=
    fun x => (IsClosed.mem_iff_infDist_zero hScl hSne).symm
  set chi : PL.E N → ℝ := fun x => Metric.infDist (f x) ((ψ.toFun '' openCube (3/4 : ℝ))ᶜ)
    with hchidef
  have hchi_eq : ∀ x, chi x = Metric.infDist (f x) ((ψ.toFun '' openCube (3/4 : ℝ))ᶜ) :=
    fun x => rfl
  set comb : PL.E N → PL.E n := fun x => bb (f x) • Gv x + (1 - bb (f x)) • f_c x
    with hcombdef
  have hcombeq : ∀ x, comb x = bb (f x) • Gv x + (1 - bb (f x)) • f_c x := fun x => rfl
  set g1 : PL.E N → M := fun x => if chi x = 0 then f x else ψ.toFun (comb x) with hg1def
  have hg1eq : ∀ x, g1 x = (if chi x = 0 then f x else ψ.toFun (comb x)) := fun x => rfl
  have hchi_ne : ∀ x, chi x ≠ 0 ↔ f x ∈ ψ.toFun '' openCube (3/4 : ℝ) := by
    intro x
    rw [hchi_eq]
    constructor
    · intro h
      by_contra hc
      exact h ((hchi_iff x).mpr hc)
    · intro h hc
      exact (hchi_iff x).mp hc h
  have hcomb_core : ∀ x, f x ∈ ψ.toFun '' closedCube (5/8 : ℝ) → comb x = Gv x := by
    intro x hx
    rw [hcombeq, hb_one (f x) hx]
    simp
  have hcomb_off : ∀ x, f x ∉ ψ.toFun '' openCube (11/16 : ℝ) → comb x = f_c x := by
    intro x hx
    rw [hcombeq, hb_zero (f x) hx]
    simp
  have hcomb_cl : ∀ x ∈ Γ₁.space, comb x ∈ closedCube (13/16 : ℝ) := by
    intro x hx i
    have hG' : |Gv x i| ≤ 13/16 := by
      have h4 : |Gv x i - gc x i| ≤ dist (Gv x) (gc x) := by
        rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (Gv x - gc x) i
      have h5 : |gc x i - f_c x i| ≤ dist (gc x) (f_c x) := by
        rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (gc x - f_c x) i
      have h6 : dist (gc x) (f_c x) < εpl := hgc_near x (hspace₁ ▸ hx)
      have h7 : |f_c x i| ≤ 3/4 := hfc_mem x i
      rw [abs_le] at h4 h5 h7 ⊢
      constructor <;> linarith [h4.1, h4.2, h5.1, h5.2, h7.1, h7.2, hGv_dist x hx, h6,
        hεpl16, hεpl0, hεgp0, hεsumsmall]
    have hf' : |f_c x i| ≤ 13/16 := le_trans (hfc_mem x i) (by norm_num)
    have hbr := hb_range (f x)
    show |bb (f x) * Gv x i + (1 - bb (f x)) * f_c x i| ≤ 13/16
    calc |bb (f x) * Gv x i + (1 - bb (f x)) * f_c x i|
        ≤ |bb (f x) * Gv x i| + |(1 - bb (f x)) * f_c x i| := abs_add_le _ _
      _ = bb (f x) * |Gv x i| + (1 - bb (f x)) * |f_c x i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hbr.1,
            abs_of_nonneg (by linarith [hbr.2] : (0:ℝ) ≤ 1 - bb (f x))]
      _ ≤ bb (f x) * (13/16) + (1 - bb (f x)) * (13/16) :=
          add_le_add (mul_le_mul_of_nonneg_left hG' hbr.1)
            (mul_le_mul_of_nonneg_left hf' (by linarith [hbr.2]))
      _ = 13/16 := by ring
  have hcomb_open : ∀ x ∈ Γ₁.space, comb x ∈ openCube (1 : ℝ) := fun x hx =>
    closedCube_subset_openCube (by norm_num : (13/16:ℝ) < 1) (hcomb_cl x hx)
  have hcomb_cont : ContinuousOn comb Γ₁.space := by
    rw [hcombdef]
    have hbf : ContinuousOn (fun x => bb (f x)) Γ₁.space :=
      hb_cont.comp_continuousOn (hspace₁ ▸ hcont)
    exact (hbf.smul hGv_cont).add ((continuousOn_const.sub hbf).smul hfc_cont.continuousOn)
  -- ===== 8. the fields =====
  have hGv_L : ∀ x ∈ L, f x ∈ ψ.toFun '' openCube (11/16 : ℝ) → Gv x = f_c x := by
    intro x hxL hfx
    have hxLt : x ∈ Lt := hmem_Lt x hxL hfx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxLt
    have hnoZ : ∀ v ∈ t, v ∉ Z := by
      intro v hv hvZ
      exact ((hZmem v).mp hvZ).2.1 (hLf_L t ht (subset_simp hv))
    have hgcx : gc x = f_c x := hgc_frz hxLt
    rw [hGveq x, Work.Engulf.Vpf.vpfApplyNotMem hZaff (hLf_faces t ht) hnoZ hxt]
    exact hgcx
  have hg1_cont : ContinuousOn g1 Γ₁.space := by
    show ContinuousOn (fun x : PL.E N => if chi x = 0 then f x else ψ.toFun (comb x)) Γ₁.space
    rw [continuousOn_iff_continuous_domRestrict]
    have hf_sub : Continuous (fun x : ↥Γ₁.space => f x) :=
      continuousOn_iff_continuous_domRestrict.mp (hspace₁ ▸ hcont)
    have hchi_sub : Continuous (fun x : ↥Γ₁.space => chi x) := by
      rw [hchidef]
      exact (Metric.continuous_infDist_pt _).comp hf_sub
    have hcomb_sub : Continuous (fun x : ↥Γ₁.space => comb x) :=
      continuousOn_iff_continuous_domRestrict.mp hcomb_cont
    have hG_sub : ContinuousOn (fun x : ↥Γ₁.space => ψ.toFun (comb x)) univ :=
      ψ.cont.comp hcomb_sub.continuousOn (fun x _ => hcomb_open x.1 x.2)
    have hg := Work.Engulf.E4Aux.continuousOn_ite_of_closure hchi_sub hf_sub.continuousOn hG_sub (by
        intro x _ hx0 hxcl
        have hsub : (fun y : ↥Γ₁.space => f y) '' {y | chi y ≠ 0} ⊆
            ψ.toFun '' openCube (3/4 : ℝ) := by
          rintro _ ⟨z, hz, rfl⟩
          exact (hchi_ne z.1).mp hz
        have hcl : f x ∈ closure (ψ.toFun '' openCube (3/4 : ℝ)) :=
          ((image_closure_subset_closure_image hf_sub).trans (closure_mono hsub))
            ⟨x, by rwa [Set.univ_inter] at hxcl, rfl⟩
        have hfx34 : f x ∈ ψ.toFun '' closedCube (3/4 : ℝ) :=
          closure_minimal (Set.image_mono (openCube_subset_closedCube (3/4)))
            (Work.Geo.Radial.isCompact_image_closedCube ψ (3/4) (by norm_num)).isClosed hcl
        have hfxCf : x.1 ∈ Cf := ⟨hspace₁ ▸ x.2, hfx34⟩
        have hcon : f x ∉ ψ.toFun '' openCube (11/16 : ℝ) := fun hc =>
          ((hchi_iff x.1).mp hx0)
            (Set.image_mono (openCube_mono (by norm_num : (11/16:ℝ) ≤ 3/4)) hc)
        rw [hcomb_off x.1 hcon, hfc_C hfxCf]
        obtain ⟨y, hy, hyψ⟩ := hfx34
        exact Work.Geo.Radial.chartInv_toFun ψ
          ⟨y, closedCube_subset_openCube (by norm_num : (3/4:ℝ) < 1) hy, hyψ⟩)
    rw [continuousOn_univ] at hg
    exact hg
  have hg1_near : ∀ x ∈ Γ₁.space, dist (g1 x) (f x) < η := by
    intro x hx
    show dist (if chi x = 0 then f x else ψ.toFun (comb x)) (f x) < η
    by_cases hchi : chi x = 0
    · rw [ite_eq_left hchi, dist_self]; exact hη0
    · rw [ite_eq_right hchi]
      have hfx : f x ∈ ψ.toFun '' openCube (3/4 : ℝ) := (hchi_ne x).mp hchi
      have hxCf : x ∈ Cf := ⟨hspace₁ ▸ hx,
        Set.image_mono (openCube_subset_closedCube (3/4)) hfx⟩
      obtain ⟨y, hy, hyψ⟩ := hfx
      have hmem : f x ∈ Work.Geo.Radial.chartImage ψ :=
        ⟨y, openCube_mono (by norm_num : (3/4:ℝ) ≤ 1) hy, hyψ⟩
      have hψ : ψ.toFun (f_c x) = f x := by
        rw [hfc_C hxCf, Work.Geo.Radial.chartInv_toFun ψ hmem]
      have hd : dist (comb x) (f_c x) < θ := by
        have hbr := hb_range (f x)
        have hsub : comb x - f_c x = bb (f x) • (Gv x - f_c x) := by
          show (bb (f x) • Gv x + (1 - bb (f x)) • f_c x) - f_c x = bb (f x) • (Gv x - f_c x)
          module
        have hnorm : ‖comb x - f_c x‖ ≤ ‖Gv x - f_c x‖ := by
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hbr.1]
          calc bb (f x) * ‖Gv x - f_c x‖ ≤ 1 * ‖Gv x - f_c x‖ :=
                mul_le_mul_of_nonneg_right hbr.2 (norm_nonneg _)
            _ = ‖Gv x - f_c x‖ := one_mul _
        have hbd : ‖Gv x - f_c x‖ ≤ εgp + εpl := by
          rw [← dist_eq_norm]
          exact (dist_triangle _ _ _).trans (add_le_add (hGv_dist x hx)
            (le_of_lt (hgc_near x (hspace₁ ▸ hx))))
        rw [dist_eq_norm]
        linarith [hnorm, hbd, hεsumθ]
      have h1 : dist (ψ.toFun (comb x)) (ψ.toFun (f_c x)) < η / 2 :=
        hθ (comb x) (hcomb_cl x hx) (f_c x)
          (closedCube_mono (by norm_num : (3/4:ℝ) ≤ 13/16) (hfc_mem x)) hd
      rw [hψ] at h1
      linarith
  have hg1_eng : X ∪ g1 '' K ⊆ V := by
    rintro z (hz | ⟨x, hxK, rfl⟩)
    · exact H7.engK (Or.inl hz)
    · by_cases hchi : chi x = 0
      · rw [hg1eq, ite_eq_left hchi]
        exact H7.engK (Or.inr ⟨x, hxK, rfl⟩)
      · have hxΓ : x ∈ Γ.space := H7.subK.subset_space hxK
        have h1 : dist (g1 x) (f x) < η := hg1_near x (hspace₁.symm ▸ hxΓ)
        have h2 : dist (g1 x) (f x) < δV :=
          lt_of_lt_of_le h1 (le_of_lt (by linarith [hηδV, hδV_pos]))
        exact hδV (Metric.mem_thickening_iff.mpr ⟨f x, ⟨x, hxK, rfl⟩, h2⟩)
  have hwit : ∀ s ∈ Γ₁.faces, f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (5/8 : ℝ) →
      ∃ M' : PL.E N →ᵃ[ℝ] PL.E n, EqOn g1 (fun x => ψ.toFun (M' x)) (PL.simp s) ∧
        ∀ x ∈ PL.simp s, M' x ∈ openCube 1 ∧ ∀ v ∈ s, M' v = vl v := by
    intro s hs hsc
    have hcore3 : f '' PL.simp s ⊆ ψ.toFun '' openCube (3/4 : ℝ) :=
      hsc.trans (Set.image_mono (closedCube_subset_openCube (by norm_num : (5/8:ℝ) < 3/4)))
    by_cases hZ : ∃ v ∈ s, v ∈ Z
    · refine ⟨Work.Engulf.Vpf.vpfA Γ₁ (Work.Engulf.Vpf.vpfC Z gc vl) s, ?_, ?_⟩
      · intro x hx
        have hfx3 : f x ∈ ψ.toFun '' openCube (3/4 : ℝ) := hcore3 ⟨x, hx, rfl⟩
        have hchi : chi x ≠ 0 := (hchi_ne x).mpr hfx3
        have hfxc : f x ∈ ψ.toFun '' closedCube (5/8 : ℝ) := hsc ⟨x, hx, rfl⟩
        rw [hg1eq, ite_eq_right hchi, hcomb_core x hfxc, hGveq,
          Work.Engulf.Vpf.vpfG'_apply_of_mem hs hZ hx]
      · intro x hx
        constructor
        · have hx₁ : x ∈ Γ₁.space := Geometry.SimplicialComplex.convexHull_subset_space hs hx
          have h5 : Work.Engulf.Vpf.vpfG' Γ₁ Z gc vl x ∈ closedCube (13/16 : ℝ) := hGv_cl x hx₁
          rw [Work.Engulf.Vpf.vpfG'_apply_of_mem hs hZ hx] at h5
          exact closedCube_subset_openCube (by norm_num : (13/16:ℝ) < 1) h5
        · intro v hv
          rw [Work.Engulf.Vpf.vpfA_apply hs hv]
          by_cases hvZ : v ∈ Z
          · rw [Work.Engulf.Vpf.vpfC_apply_of_mem hvZ]
          · rw [Work.Engulf.Vpf.vpfC_apply_of_notMem hvZ]
            have hmem : v ∈ Vt := (hVt_mem v).mpr ⟨s, hs, hv⟩
            have hFz : v ∈ Fzv := by
              by_contra hc
              exact hvZ ((hZnotFz v hmem).mpr hc)
            exact (hvl_frz v hFz).symm
    · push_neg at hZ
      have hsne : s.Nonempty := Geometry.SimplicialComplex.nonempty_of_mem_faces hs
      obtain ⟨x0, hx0⟩ := simp_nonempty hsne
      have hx0Γ : x0 ∈ Γ₁.space :=
        Geometry.SimplicialComplex.convexHull_subset_space hs hx0
      have hf0 : f x0 ∈ ψ.toFun '' closedCube (5/8 : ℝ) := hsc ⟨x0, hx0, rfl⟩
      have hx0Cf : x0 ∈ Cf := ⟨hspace₁ ▸ hx0Γ,
        Set.image_mono (closedCube_mono (by norm_num : (5/8:ℝ) ≤ 3/4)) hf0⟩
      have hfc0 : f_c x0 ∈ closedCube (5/8 : ℝ) :=
        hfc_core x0 (hspace₁ ▸ hx0Γ) hf0
      have hgc0 : gc x0 ∈ closedCube (11/16 : ℝ) := by
        intro i
        have h1 : |gc x0 i - f_c x0 i| ≤ dist (gc x0) (f_c x0) := by
          rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (gc x0 - f_c x0) i
        have h2 : dist (gc x0) (f_c x0) < εpl := hgc_near x0 (hspace₁ ▸ hx0Γ)
        have h3 : |f_c x0 i| ≤ 5/8 := hfc0 i
        rw [abs_le] at h1 h3 ⊢
        constructor <;> linarith [h1.1, h1.2, h3.1, h3.2, h2, hεpl16, hεpl0]
      obtain ⟨A, hA⟩ := hgc_aff s hs ⟨x0, hx0, hgc0⟩
      refine ⟨A, ?_, ?_⟩
      · intro x hx
        have hfx3 : f x ∈ ψ.toFun '' openCube (3/4 : ℝ) := hcore3 ⟨x, hx, rfl⟩
        have hchi : chi x ≠ 0 := (hchi_ne x).mpr hfx3
        have hfxc : f x ∈ ψ.toFun '' closedCube (5/8 : ℝ) := hsc ⟨x, hx, rfl⟩
        rw [hg1eq, ite_eq_right hchi, hcomb_core x hfxc, hGveq,
          Work.Engulf.Vpf.vpfApplyNotMem hZaff hs hZ hx]
        exact congrArg ψ.toFun (hA hx)
      · intro x hx
        constructor
        · have hx₁ : x ∈ Γ₁.space := Geometry.SimplicialComplex.convexHull_subset_space hs hx
          have h2 : gc x = A x := hA hx
          rw [← h2]
          exact closedCube_subset_openCube (by norm_num : (13/16:ℝ) < 1) (hgc_cl x hx₁)
        · intro v hv
          have hmem : v ∈ Vt := (hVt_mem v).mpr ⟨s, hs, hv⟩
          have hFz : v ∈ Fzv := by
            by_contra hc
            exact hZ v hv ((hZnotFz v hmem).mpr hc)
          have h2 : gc v = A v := hA (subset_simp hv)
          exact h2.symm.trans (hvl_frz v hFz).symm
  -- `mesh`
  have hmesh_field : ∀ s ∈ Γ₁.faces, f '' PL.simp s ⊆ ψ.toFun '' closedCube (5/8 : ℝ) ∨
      ∀ x ∈ PL.simp s, g1 x ∉ ψ.toFun '' closedCube (9/16 : ℝ) := by
    intro s hs
    by_cases hcore : f '' PL.simp s ⊆ ψ.toFun '' closedCube (5/8 : ℝ)
    · exact Or.inl hcore
    · refine Or.inr fun x hx hx9 => hcore ?_
      have hxΓ₁ : x ∈ Γ₁.space := Geometry.SimplicialComplex.convexHull_subset_space hs hx
      have hnear : dist (f x) (g1 x) < ρf / 2 :=
        lt_of_lt_of_le (by rw [dist_comm]; exact hg1_near x hxΓ₁) hηρf
      intro z hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hzΓ : z' ∈ Γ.space := hspace₁ ▸
        Geometry.SimplicialComplex.convexHull_subset_space hs hz'
      have hxΓ : x ∈ Γ.space := hspace₁ ▸ hxΓ₁
      have hdist : dist (f z') (f x) < ρf / 2 :=
        lt_of_lt_of_le (hosc_f s hs z' hz' x hx) hδosc_ρf
      exact hρf (g1 x) hx9 (f z') (by
        calc dist (f z') (g1 x) ≤ dist (f z') (f x) + dist (f x) (g1 x) := dist_triangle _ _ _
          _ < ρf := by linarith [hdist, hnear])
  -- the frozen region
  set Rc : Set (PL.E N) := ⋃ s ∈ hΓ₁fin.toFinset.filter
    (fun s => ∃ x ∈ PL.simp s, g1 x ∈ ψ.toFun '' closedCube (5/8 : ℝ)), PL.simp s with hRcdef
  have hRc_mem : ∀ x ∈ Γ₁.space, g1 x ∈ ψ.toFun '' closedCube (5/8 : ℝ) → x ∈ Rc := by
    intro x hx hx5
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr
      ⟨(Set.Finite.mem_toFinset hΓ₁fin).mpr hs, ⟨x, hxs, hx5⟩⟩, hxs⟩
  have hRc_face : ∀ s ∈ Γ₁.faces, (∃ x ∈ PL.simp s, g1 x ∈ ψ.toFun '' closedCube (5/8 : ℝ)) →
      PL.simp s ⊆ Rc := by
    intro s hs hcon y hy
    exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr
      ⟨(Set.Finite.mem_toFinset hΓ₁fin).mpr hs, hcon⟩, hy⟩
  have hRc_sub : IsSubSp Γ₁ Rc := by
    constructor
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
      exact Geometry.SimplicialComplex.convexHull_subset_space
        ((Set.Finite.mem_toFinset hΓ₁fin).mp (Finset.mem_filter.mp hs).1) hxs
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨s, (Set.Finite.mem_toFinset hΓ₁fin).mp (Finset.mem_filter.mp hs).1, hxs,
        fun y hy => Set.mem_iUnion₂.mpr ⟨s, hs, hy⟩⟩
  have hhalfcube : ∀ s ∈ Γ₁.faces, f '' PL.simp s ⊆ ψ.toFun '' openCube (1/2 : ℝ) →
      PL.simp s ⊆ L ∪ Rc := by
    intro s hs hfs x hx
    by_cases hxL : x ∈ L
    · exact Or.inl hxL
    · refine Or.inr (hRc_mem x (Geometry.SimplicialComplex.convexHull_subset_space hs hx) ?_)
      have hfx : f x ∈ ψ.toFun '' openCube (1/2 : ℝ) := hfs ⟨x, hx, rfl⟩
      have hfx5 : f x ∈ ψ.toFun '' closedCube (5/8 : ℝ) :=
        Set.image_mono ((openCube_mono (by norm_num : (1/2:ℝ) ≤ 5/8)).trans
          (openCube_subset_closedCube (5/8))) hfx
      by_cases hchi : chi x = 0
      · rw [hg1eq, ite_eq_left hchi]
        exact hfx5
      · rw [hg1eq, ite_eq_right hchi]
        have h1 : dist (ψ.toFun (comb x)) (f x) < η := by
          have h2 : dist (g1 x) (f x) < η :=
            hg1_near x (Geometry.SimplicialComplex.convexHull_subset_space hs hx)
          rwa [show g1 x = ψ.toFun (comb x) from by rw [hg1eq, ite_eq_right hchi]] at h2
        exact hρh (f x) (Set.image_mono (openCube_subset_closedCube (1/2)) hfx)
          (ψ.toFun (comb x)) (lt_of_lt_of_le h1 (by linarith [hηρh, hρh_pos]))
  have hFzv_hull : ∀ s ∈ Γ₁.faces, f '' PL.simp s ⊆ ψ.toFun '' closedCube (5/8 : ℝ) →
      PL.simp (s ∩ Fzv) ⊆ L := by
    intro s hs hsc
    by_cases hne : (s ∩ Fzv).Nonempty
    · refine (T N).full R Γ hΓfin L hsubL hR1 s hs (s ∩ Fzv) Finset.inter_subset_left hne ?_
      intro v hv
      have hv' : v ∈ s ∩ Fzv := hv
      obtain ⟨hvs, hvFz⟩ := Finset.mem_inter.mp hv'
      rcases (hFzmem v).mp hvFz with ⟨-, hL | hnc⟩
      · exact hL
      · exact absurd (hsc ⟨v, subset_simp hvs, rfl⟩) hnc
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, simp_empty]
      exact Set.empty_subset _
  -- general position
  have hgp_lift : ∀ u ∈ Vt, u ∉ Fzv → ∀ T' : Finset (PL.E N), (∀ v ∈ T', v ∈ Vt) → u ∉ T' →
      vl u ∈ (affineSpan ℝ (vl '' (T' : Set (PL.E N))) : Set (PL.E n)) →
      affineSpan ℝ (vl '' (T' : Set (PL.E N))) = ⊤ := by
    intro u huVt huFz T' hTVt huT hmem
    have himg : vl '' (T' : Set (PL.E N)) = yy '' ↑(subV Vt T' hTVt) := by
      rw [hvldef]
      exact image_lift_eq Vt yy T' hTVt
    have hu' : (⟨u, huVt⟩ : ↥Vt) ∉ subV Vt T' hTVt := by
      rw [mem_subV]; exact huT
    have hfz' : (⟨u, huVt⟩ : ↥Vt) ∉ fz := by
      rw [hfz_mem]; exact huFz
    have hmem' : yy ⟨u, huVt⟩ ∈ (affineSpan ℝ (yy '' ↑(subV Vt T' hTVt)) : Set (PL.E n)) := by
      rw [← hvl_eq ⟨u, huVt⟩, ← himg]; exact hmem
    have := hyy_gp ⟨u, huVt⟩ hfz' (subV Vt T' hTVt) hu' hmem'
    rw [himg]; exact this
  have hgp_liftS : ∀ u ∈ Vt, u ∉ Fzv → ∀ T' : Finset (PL.E N), (∀ v ∈ T', v ∈ Vt) → u ∉ T' →
      ∀ S ∈ Xcov, vl u ∈ (affineSpan ℝ ((vl '' (T' : Set (PL.E N))) ∪ (S : Set (PL.E n))) :
          Set (PL.E n)) →
      affineSpan ℝ ((vl '' (T' : Set (PL.E N))) ∪ (S : Set (PL.E n))) = ⊤ := by
    intro u huVt huFz T' hTVt huT S hS hmem
    have himg : vl '' (T' : Set (PL.E N)) = yy '' ↑(subV Vt T' hTVt) := by
      rw [hvldef]
      exact image_lift_eq Vt yy T' hTVt
    have hu' : (⟨u, huVt⟩ : ↥Vt) ∉ subV Vt T' hTVt := by rw [mem_subV]; exact huT
    have hfz' : (⟨u, huVt⟩ : ↥Vt) ∉ fz := by rw [hfz_mem]; exact huFz
    have hmem' : yy ⟨u, huVt⟩ ∈ (affineSpan ℝ ((yy '' ↑(subV Vt T' hTVt)) ∪ (S : Set (PL.E n))) :
        Set (PL.E n)) := by
      rw [← hvl_eq ⟨u, huVt⟩, ← himg]; exact hmem
    have := hyy_gpS ⟨u, huVt⟩ hfz' (subV Vt T' hTVt) hu' S hS hmem'
    rw [himg]; exact this
  have hA_image : ∀ (σ : Finset (PL.E N)) (M' : PL.E N →ᵃ[ℝ] PL.E n), (∀ v ∈ σ, M' v = vl v) →
      M' '' PL.simp σ = Work.PL.Generic.hullOf vl σ := by
    intro σ M' hM'
    rw [Work.PL.Generic.hullOf_eq_simp]
    have h1 : M' '' PL.simp σ = PL.simp (σ.image M') := by
      rw [PL.simp, AffineMap.image_convexHull, PL.simp]
      congr 1
      rw [Finset.coe_image]
    rw [h1]
    congr 1
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, (hM' v hv).symm⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, (hM' v hv)⟩
  have hindep : ∀ (σ : Finset (PL.E N)) (M' : PL.E N →ᵃ[ℝ] PL.E n), σ.card ≤ n + 1 →
      (∀ v ∈ σ, v ∈ Vt) → (∀ v ∈ σ, M' v = vl v) →
      AffineIndependent ℝ (fun v : ↥(σ ∩ Fzv) => vl v) → Set.InjOn M' (PL.simp σ) := by
    intro σ M' hcard hVσ hM' hind
    have hvlind : AffineIndependent ℝ (fun v : ↥σ => vl v) :=
      affineIndependent_of_gp_Vt Fzv vl σ hVσ hcard
        (fun u huVt huFz T' hTσ huT hmem =>
          hgp_lift u huVt huFz T' (fun v hv => hVσ v (hTσ hv)) huT hmem) hind
    have hAind : AffineIndependent ℝ (fun v : ↥σ => M' v) := by
      have hfun : (fun v : ↥σ => M' v) = (fun v : ↥σ => vl v) := funext fun v => hM' v v.2
      rw [hfun]; exact hvlind
    exact Work.Engulf.E4Aux.injOn_of_affineIndependent_image hAind
  have hpair : ∀ (σ₁ σ₂ : Finset (PL.E N)) (A₁ A₂ : PL.E N →ᵃ[ℝ] PL.E n),
      σ₁.card ≤ n + 1 → σ₂.card ≤ n + 1 → (∀ v ∈ σ₁, v ∈ Vt) → (∀ v ∈ σ₂, v ∈ Vt) →
      (∀ v ∈ σ₁, A₁ v = vl v) → (∀ v ∈ σ₂, A₂ v = vl v) →
      (∀ z ∈ A₁ '' PL.simp (σ₁ ∩ Fzv) ∩ A₂ '' PL.simp (σ₂ ∩ Fzv),
        (∃ v ∈ σ₁ ∩ σ₂, v ∉ Fzv) → z ∈ A₁ '' PL.simp (σ₁ ∩ σ₂ ∩ Fzv)) →
      ∃ D : Set (PL.E n), PL.DomDim D ((σ₁.card : ℤ) + (σ₂.card : ℤ) - 2 - (n : ℤ)) ∧
        A₁ '' PL.simp σ₁ ∩ A₂ '' PL.simp σ₂ ⊆
          A₁ '' PL.simp (σ₁ ∩ σ₂) ∪ (A₁ '' PL.simp (σ₁ ∩ Fzv) ∩ A₂ '' PL.simp (σ₂ ∩ Fzv)) ∪ D := by
    intro σ₁ σ₂ A₁ A₂ hc1 hc2 hV1 hV2 hA1 hA2 hcol
    have e1 := hA_image σ₁ A₁ hA1
    have e2 := hA_image σ₂ A₂ hA2
    have ei := hA_image (σ₁ ∩ σ₂) A₁ (fun v hv => hA1 v (Finset.mem_inter.mp hv).1)
    have ef1 := hA_image (σ₁ ∩ Fzv) A₁ (fun v hv => hA1 v (Finset.mem_inter.mp hv).1)
    have ef2 := hA_image (σ₂ ∩ Fzv) A₂ (fun v hv => hA2 v (Finset.mem_inter.mp hv).1)
    have efi := hA_image (σ₁ ∩ σ₂ ∩ Fzv) A₁
      (fun v hv => hA1 v (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).1)
    have hh1 : Work.PL.Generic.hullOf vl σ₁ = Work.PL.Generic.hullOf yy (subV Vt σ₁ hV1) := by
      rw [Work.PL.Generic.hullOf, Work.PL.Generic.hullOf,
        show vl '' (σ₁ : Set (PL.E N)) = yy '' ↑(subV Vt σ₁ hV1) from by
          rw [hvldef]
          exact image_lift_eq Vt yy σ₁ hV1]
    have hh2 : Work.PL.Generic.hullOf vl σ₂ = Work.PL.Generic.hullOf yy (subV Vt σ₂ hV2) := by
      rw [Work.PL.Generic.hullOf, Work.PL.Generic.hullOf,
        show vl '' (σ₂ : Set (PL.E N)) = yy '' ↑(subV Vt σ₂ hV2) from by
          rw [hvldef]
          exact image_lift_eq Vt yy σ₂ hV2]
    have hsubV_int : subV Vt σ₁ hV1 ∩ subV Vt σ₂ hV2 = subV Vt (σ₁ ∩ σ₂)
        (fun v hv => hV1 v (Finset.mem_inter.mp hv).1) := by
      ext w
      rw [Finset.mem_inter, mem_subV, mem_subV, mem_subV, Finset.mem_inter]
    have hsubV_fz1 : subV Vt σ₁ hV1 ∩ fz = subV Vt (σ₁ ∩ Fzv)
        (fun v hv => hV1 v (Finset.mem_inter.mp hv).1) := by
      ext w
      rw [Finset.mem_inter, mem_subV, hfz_mem, mem_subV, Finset.mem_inter]
    have hsubV_fz2 : subV Vt σ₂ hV2 ∩ fz = subV Vt (σ₂ ∩ Fzv)
        (fun v hv => hV2 v (Finset.mem_inter.mp hv).1) := by
      ext w
      rw [Finset.mem_inter, mem_subV, hfz_mem, mem_subV, Finset.mem_inter]
    have hsubV_fzi : subV Vt (σ₁ ∩ σ₂) (fun v hv => hV1 v (Finset.mem_inter.mp hv).1) ∩ fz =
        subV Vt (σ₁ ∩ σ₂ ∩ Fzv)
          (fun v hv => hV1 v (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).1) := by
      ext w
      simp only [Finset.mem_inter, mem_subV, hfz_mem]
    have hhf1 : Work.PL.Generic.hullOf vl (σ₁ ∩ Fzv) =
        Work.PL.Generic.hullOf yy (subV Vt σ₁ hV1 ∩ fz) := by
      rw [hsubV_fz1, Work.PL.Generic.hullOf, Work.PL.Generic.hullOf]
      congr 1
      rw [hvldef]
      exact image_lift_eq Vt yy (σ₁ ∩ Fzv) _
    have hhf2 : Work.PL.Generic.hullOf vl (σ₂ ∩ Fzv) =
        Work.PL.Generic.hullOf yy (subV Vt σ₂ hV2 ∩ fz) := by
      rw [hsubV_fz2, Work.PL.Generic.hullOf, Work.PL.Generic.hullOf]
      congr 1
      rw [hvldef]
      exact image_lift_eq Vt yy (σ₂ ∩ Fzv) _
    have hhi : Work.PL.Generic.hullOf vl (σ₁ ∩ σ₂) =
        Work.PL.Generic.hullOf yy (subV Vt σ₁ hV1 ∩ subV Vt σ₂ hV2) := by
      rw [hsubV_int, Work.PL.Generic.hullOf, Work.PL.Generic.hullOf]
      congr 1
      rw [hvldef]
      exact image_lift_eq Vt yy (σ₁ ∩ σ₂) _
    have hhfi : Work.PL.Generic.hullOf vl (σ₁ ∩ σ₂ ∩ Fzv) =
        Work.PL.Generic.hullOf yy (subV Vt σ₁ hV1 ∩ subV Vt σ₂ hV2 ∩ fz) := by
      rw [hsubV_int, hsubV_fzi, Work.PL.Generic.hullOf, Work.PL.Generic.hullOf]
      congr 1
      rw [hvldef]
      exact image_lift_eq Vt yy (σ₁ ∩ σ₂ ∩ Fzv) _
    have hcol' : ∀ z ∈ Work.PL.Generic.hullOf yy (subV Vt σ₁ hV1 ∩ fz) ∩
        Work.PL.Generic.hullOf yy (subV Vt σ₂ hV2 ∩ fz),
        (∃ v ∈ subV Vt σ₁ hV1 ∩ subV Vt σ₂ hV2, v ∉ fz) →
        z ∈ Work.PL.Generic.hullOf yy
          (subV Vt σ₁ hV1 ∩ subV Vt σ₂ hV2 ∩ fz) := by
      rintro z hz ⟨v, hv, hvfz⟩
      rw [← hhf1, ← hhf2] at hz
      rw [← ef1, ← ef2] at hz
      rw [← hhfi, ← efi]
      refine hcol z hz ?_
      obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
      exact ⟨v.1, Finset.mem_inter.mpr ⟨(mem_subV hV1 v).mp hv1, (mem_subV hV2 v).mp hv2⟩,
        fun hvz => hvfz ((hfz_mem v).mpr hvz)⟩
    obtain ⟨D, hDdom, hDsub⟩ := Work.PL.Generic.gp_pairs_pairwise fz yy
      (subV Vt σ₁ hV1) (subV Vt σ₂ hV2)
      (fun u hu T' hT huT hm => hyy_gp u hu T' huT hm) hcol'
    have hc1 : (subV Vt σ₁ hV1).card = σ₁.card := by
      rw [subV, Finset.card_map, Finset.card_attach]
    have hc2 : (subV Vt σ₂ hV2).card = σ₂.card := by
      rw [subV, Finset.card_map, Finset.card_attach]
    refine ⟨D, ?_, ?_⟩
    · rw [hc1, hc2] at hDdom; exact hDdom
    · rw [e1, hh1, e2, hh2, ei, hhi, ef1, hhf1, ef2, hhf2]; exact hDsub
  have hfixed : ∀ (σ S : Finset (PL.E N)) (M' : PL.E N →ᵃ[ℝ] PL.E n) (T' : Finset (PL.E n)),
      σ.card ≤ n + 1 → (∀ v ∈ σ, v ∈ Vt) → (∀ v ∈ σ, M' v = vl v) →
      AffineIndependent ℝ (fun v : ↥(σ ∩ Fzv) => vl v) → T' ∈ Xcov →
      ∃ D : Set (PL.E n), PL.DomDim D ((σ.card : ℤ) + (T'.card : ℤ) - 2 - (n : ℤ)) ∧
        M' '' PL.simp σ ∩ PL.simp T' ⊆ M' '' PL.simp (σ ∩ Fzv) ∪ D := by
    intro σ S M' T' hcard hVσ hM' hind hT
    have e1 := hA_image σ M' hM'
    have ef1 := hA_image (σ ∩ Fzv) M' (fun v hv => hM' v (Finset.mem_inter.mp hv).1)
    have hh1 : Work.PL.Generic.hullOf vl σ = Work.PL.Generic.hullOf yy (subV Vt σ hVσ) := by
      rw [Work.PL.Generic.hullOf, Work.PL.Generic.hullOf,
        show vl '' (σ : Set (PL.E N)) = yy '' ↑(subV Vt σ hVσ) from by
          rw [hvldef]
          exact image_lift_eq Vt yy σ hVσ]
    have hsubV_fz1 : subV Vt σ hVσ ∩ fz = subV Vt (σ ∩ Fzv)
        (fun v hv => hVσ v (Finset.mem_inter.mp hv).1) := by
      ext w
      rw [Finset.mem_inter, mem_subV, hfz_mem, mem_subV, Finset.mem_inter]
    have hnd' : AffineIndependent ℝ (fun v : ↥(subV Vt σ hVσ ∩ fz) => yy v) := by
      rw [hsubV_fz1]
      let ee : ↥(σ ∩ Fzv) ≃ ↥(subV Vt (σ ∩ Fzv) (fun v hv => hVσ v (Finset.mem_inter.mp hv).1)) :=
        { toFun := fun v => ⟨⟨v.1, (fun v hv => hVσ v (Finset.mem_inter.mp hv).1) v.1 v.2⟩, by
            rw [mem_subV]; exact v.2⟩
          invFun := fun w => ⟨w.1.1,
            (mem_subV (fun v hv => hVσ v (Finset.mem_inter.mp hv).1) w.1).mp w.2⟩
          left_inv := fun v => Subtype.ext rfl
          right_inv := fun w => Subtype.ext (Subtype.ext rfl) }
      refine affineIndependent_comp_equiv ee (fun w => yy w) (fun v : ↥(σ ∩ Fzv) => vl ↑v) ?_ hind
      intro v
      exact (hvl_eq ⟨v.1, (fun v hv => hVσ v (Finset.mem_inter.mp hv).1) v.1 v.2⟩).symm
    have hhf1 : Work.PL.Generic.hullOf vl (σ ∩ Fzv) =
        Work.PL.Generic.hullOf yy (subV Vt σ hVσ ∩ fz) := by
      rw [hsubV_fz1, Work.PL.Generic.hullOf, Work.PL.Generic.hullOf]
      congr 1
      rw [hvldef]
      exact image_lift_eq Vt yy (σ ∩ Fzv) _
    have hvlind : AffineIndependent ℝ (fun v : ↥(subV Vt σ hVσ) => yy v) :=
      Work.PL.Generic.affineIndependent_of_gp fz yy (subV Vt σ hVσ)
        (by rw [subV, Finset.card_map, Finset.card_attach]; exact hcard)
        (fun u hu T'' hT'' huT hm => hyy_gp u hu T'' huT hm) hnd'
    obtain ⟨D, hDdom, hDsub⟩ := Work.PL.Generic.gp_pairs_fixed fz yy (subV Vt σ hVσ) T'
      (fun u hu T'' _ huT hm => hyy_gp u hu T'' huT hm)
      (fun u hu T'' _ huT hm => hyy_gpS u hu T'' huT T' hT hm) hvlind
    have hc1 : (subV Vt σ hVσ).card = σ.card := by
      rw [subV, Finset.card_map, Finset.card_attach]
    refine ⟨D, ?_, ?_⟩
    · rw [hc1] at hDdom; exact hDdom
    · rw [e1, hh1, ef1, hhf1]; exact hDsub
  have hg1_frz : Set.EqOn g1 f L := by
    intro x hxL
    by_cases hchi : chi x = 0
    · rw [hg1eq, ite_eq_left hchi]
    · rw [hg1eq, ite_eq_right hchi]
      have hfx : f x ∈ ψ.toFun '' openCube (3/4 : ℝ) := (hchi_ne x).mp hchi
      have hxCf : x ∈ Cf := ⟨hsubL.subset_space hxL,
        Set.image_mono (openCube_subset_closedCube (3/4)) hfx⟩
      have hmem : f x ∈ Work.Geo.Radial.chartImage ψ := by
        obtain ⟨y, hy, hyψ⟩ := hfx
        exact ⟨y, openCube_mono (by norm_num : (3/4:ℝ) ≤ 1) hy, hyψ⟩
      have hcombx : comb x = f_c x := by
        by_cases hbb : bb (f x) = 0
        · rw [hcombeq, hbb]; simp
        · have hfx11 : f x ∈ ψ.toFun '' openCube (11/16 : ℝ) := by
            by_contra hcon
            exact hbb (hb_zero (f x) hcon)
          have hGvx : Gv x = f_c x := hGv_L x hxL hfx11
          rw [hcombeq, hGvx]
          module
      rw [hcombx, hfc_C hxCf]
      exact Work.Geo.Radial.chartInv_toFun ψ hmem
  let D : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε :=
    { η := η, hη0 := hη0, hη16 := hη16, hηε := hηε, Γ₁ := Γ₁, hΓ₁ := hΓ₁fin, sub := hsub₁, subsp := fun S hS => (T N).subdiv.subsp R Γ hΓfin S hS, carrier := fun s hs hsL => by rw [hΓ₁def] at hs; exact (T N).carrier R Γ hΓfin L H7.cfg.subL s hs hsL, ord := ord, ord_mem := hord_mem₁, ord_card := hord_card, ord_sub := hord_sub, ord_cov := hord_cov₁, ord_split := fun i hi => hord_split i hi, g₁ := g1, g₁cont := hg1_cont, g₁frz := hg1_frz, g₁near := hg1_near, g₁_eng := hg1_eng, Vt := Vt, Vt_mem := hVt_mem, Rc := Rc, Rc_sub := hRc_sub, Rc_mem := hRc_mem, Rc_face := hRc_face, halfcube_frz := hhalfcube, vv := vl, wit := hwit, mesh := hmesh_field, shell17 := hshell17, Fzv := Fzv, Fzv_sub := hFzv_sub, Fzv_hull := hFzv_hull, indep := hindep, pair := hpair, Xcov := Xcov, Xcov_card := hXcov_card, Xcov_cov := hXcov_cov, fixed := hfixed }
  -- ===== the two extra NormData facts (lead's `NOTES_LEAD_poincare_E4c.md` §A.2) =====
  have hcore11Local : ∀ x ∈ Γ₁.space, f x ∈ ψ.toFun '' closedCube (5 / 8 : ℝ) →
      g1 x ∈ ψ.toFun '' closedCube (11 / 16 : ℝ) := by
    intro x hxΓ hfx
    have hfx' := hfx
    have hxΓ' : x ∈ Γ.space := hspace₁ ▸ hxΓ
    obtain ⟨y, hy, hyψ⟩ := hfx
    have hfx34 : f x ∈ ψ.toFun '' openCube (3 / 4 : ℝ) :=
      ⟨y, closedCube_subset_openCube (by norm_num : (5 / 8 : ℝ) < 3 / 4) hy, hyψ⟩
    have hchi : chi x ≠ 0 := (hchi_ne x).mpr hfx34
    have hg1x : g1 x = ψ.toFun (Gv x) := by
      rw [hg1eq, ite_eq_right hchi, hcomb_core x hfx']
    have hGv : Gv x ∈ closedCube (11 / 16 : ℝ) := by
      intro i
      have h1 : |Gv x i - f_c x i| ≤ dist (Gv x) (f_c x) := by
        rw [dist_eq_norm]; simpa using PiLp.norm_apply_le (Gv x - f_c x) i
      have h2 : dist (gc x) (f_c x) < εpl := hgc_near x (hspace₁ ▸ hxΓ)
      have h3 : |f_c x i| ≤ 5 / 8 := hfc_core x hxΓ' hfx' i
      have h4 : dist (Gv x) (f_c x) ≤ εgp + εpl :=
        le_trans (dist_triangle _ _ _) (add_le_add (hGv_dist x hxΓ) h2.le)
      have h5 := abs_le.mp (le_trans h1 h4)
      have h3' := abs_le.mp h3
      rw [abs_le]
      constructor <;> linarith [h5.1, h5.2, h3'.1, h3'.2, hεsumsmall]
    rw [hg1x]
    exact ⟨Gv x, hGv, rfl⟩
  have hcarrierSLocal : ∀ S : Set (PL.E N), IsSubSp Γ S → ∀ s ∈ Γ₁.faces, simp s ⊆ S →
      ∃ t ∈ Γ.faces, simp s ⊆ simp t ∧ simp t ⊆ S := by
    intro S hS s hs hsS
    rw [hΓ₁def] at hs
    exact (T N).carrier R Γ hΓfin S hS s hs hsS
  exact ⟨D, hcore11Local, hcarrierSLocal⟩

end Work.Engulf.E4alt
