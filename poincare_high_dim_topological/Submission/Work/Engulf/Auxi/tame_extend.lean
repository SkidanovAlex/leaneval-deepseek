import Mathlib
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.subcube_chart
import Submission.Work.PL.Subdiv.DomDim.domDim_affine_image

/-!
# `tame_extend` (Hx2d′, replacing Hx2d)
-/

open Set Metric PL

namespace Work.Engulf.Aux

variable {n p N : ℕ} {M : Type*} [MetricSpace M]

/-! ### Compact images of subcomplexes -/

theorem isCompact_image_of_isSubSp {Γ : PL.Cx N} {T : Set (PL.E N)} {f : PL.E N → M}
    (hfin : Γ.faces.Finite) (hcont : ContinuousOn f Γ.space) (hT : Work.Engulf.IsSubSp Γ T) :
    IsCompact (f '' T) :=
  (Work.Engulf.isCompact_of_isSubSp hfin hT).image_of_continuousOn (hcont.mono hT.subset_space)

theorem exists_ball_disjoint_of_isCompact {K : Set M} (hK : IsCompact K) {x : M} (hx : x ∉ K) :
    ∃ η > 0, Disjoint (ball x η) K := by
  have hopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  obtain ⟨η, hη, hsub⟩ := Metric.isOpen_iff.mp hopen x hx
  exact ⟨η, hη, Set.disjoint_left.mpr fun a ha haK => hsub ha haK⟩

/-! ### The affine map `w ↦ t⁻¹ • (w - c)` -/

noncomputable def affSubSmul (c : PL.E n) (t : ℝ) : PL.E n →ᵃ[ℝ] PL.E n :=
  AffineMap.mk' (fun w => t⁻¹ • (w - c)) (t⁻¹ • (LinearMap.id : PL.E n →ₗ[ℝ] PL.E n)) 0
    (by
      intro p'
      simp only [LinearMap.smul_apply, LinearMap.id_apply, vsub_eq_sub, vadd_eq_add, sub_zero]
      module)

theorem affSubSmul_apply (c : PL.E n) (t : ℝ) (w : PL.E n) :
    affSubSmul c t w = t⁻¹ • (w - c) := rfl

theorem affSubSmul_injective (c : PL.E n) {t : ℝ} (ht : t ≠ 0) :
    Function.Injective (affSubSmul c t) := by
  intro x y h
  rw [affSubSmul_apply, affSubSmul_apply] at h
  have h2 : x - c = y - c := by
    have hh := congrArg (fun z : PL.E n => t • z) h
    simpa only [smul_smul, mul_inv_cancel₀ ht, one_smul] using hh
  exact sub_left_injective h2

theorem affSubSmul_id (c : PL.E n) {t : ℝ} (ht : t ≠ 0) (y : PL.E n) :
    affSubSmul c t (c + t • y) = y := by
  rw [affSubSmul_apply, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-! ### Chart injectivity on the cube -/

theorem CubeChart.injOn_openCube (ψ : PL.CubeChart n M) {x y : PL.E n}
    (hx : x ∈ PL.openCube (n := n) 1) (hy : y ∈ PL.openCube (n := n) 1)
    (h : ψ.toFun x = ψ.toFun y) : x = y := by
  have h' : (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨x, hx⟩
      = (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨y, hy⟩ := h
  exact congrArg Subtype.val (ψ.emb.toIsEmbedding.injective h')

/-! ### Sub-cube maps on the closed cube -/

theorem subcube_maps_closedCube {c : PL.E n} {ρ t r r' : ℝ}
    (hc : c ∈ PL.closedCube (n := n) ρ) (ht0 : 0 ≤ t) (hrr' : ρ + t * r ≤ r') :
    ∀ z ∈ PL.closedCube (n := n) r, c + t • z ∈ PL.closedCube (n := n) r' := by
  intro z hz i
  have hzi : |z i| ≤ r := hz i
  have hci : |c i| ≤ ρ := hc i
  have hcoord : (c + t • z) i = c i + t * z i := by simp [PiLp.add_apply, PiLp.smul_apply]
  rw [hcoord]
  calc |c i + t * z i| ≤ |c i| + |t * z i| := abs_add_le _ _
    _ = |c i| + t * |z i| := by rw [abs_mul, abs_of_nonneg ht0]
    _ ≤ ρ + t * r := by
        have h2 : t * |z i| ≤ t * r := mul_le_mul_of_nonneg_left hzi ht0
        linarith
    _ ≤ r' := hrr'

theorem subcube_maps_closedCube_open {c : PL.E n} {ρ t r r' : ℝ}
    (hc : c ∈ PL.closedCube (n := n) ρ) (ht0 : 0 ≤ t) (hrr' : ρ + t * r < r') :
    ∀ z ∈ PL.closedCube (n := n) r, c + t • z ∈ PL.openCube (n := n) r' := by
  intro z hz i
  have hzi : |z i| ≤ r := hz i
  have hci : |c i| ≤ ρ := hc i
  have hcoord : (c + t • z) i = c i + t * z i := by simp [PiLp.add_apply, PiLp.smul_apply]
  rw [hcoord]
  have hle : |c i + t * z i| ≤ ρ + t * r := by
    calc |c i + t * z i| ≤ |c i| + |t * z i| := abs_add_le _ _
      _ = |c i| + t * |z i| := by rw [abs_mul, abs_of_nonneg ht0]
      _ ≤ ρ + t * r := by
          have h2 : t * |z i| ≤ t * r := mul_le_mul_of_nonneg_left hzi ht0
          linarith
  linarith

/-! ### The open affine image of the open cube -/

theorem isOpen_affineImage_openCube {c : PL.E n} {t : ℝ} (ht : 0 < t) :
    IsOpen ((fun w : PL.E n => c + t • w) '' PL.openCube (n := n) 1) := by
  have hmap : IsOpenMap (fun w : PL.E n => c + t • w) := by
    have h1 : (fun w : PL.E n => c + t • w)
        = ⇑((Homeomorph.smulOfNeZero t (ne_of_gt ht)).trans (Homeomorph.addLeft c)) := by
      funext w; simp [Homeomorph.trans_apply]
    rw [h1]; exact Homeomorph.isOpenMap _
  exact hmap _ (Work.Engulf.isOpen_openCube 1)

/-! ### A positive scale keeping a bounded set near a point -/

theorem exists_pos_smul_closedCube_subset_ball {c : PL.E n} {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₀ : ℝ, t₀ > 0 ∧ ∀ (t : ℝ), 0 ≤ t → t ≤ t₀ → ∀ y ∈ PL.closedCube (n := n) 1,
      dist (c + t • y) c < δ := by
  have hb : Bornology.IsBounded (PL.closedCube (n := n) 1) :=
    (Work.Engulf.isCompact_closedCube (N := n) 1).isBounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  have hC0 : 0 ≤ C := by
    have h := hC 0 (by intro i; simp)
    simpa using h
  refine ⟨δ / (C + 1), by positivity, ?_⟩
  intro t ht0 ht y hy
  rw [dist_eq_norm]
  have hsub : c + t • y - c = t • y := by abel
  rw [hsub, norm_smul, Real.norm_of_nonneg ht0]
  have hyC : ‖y‖ ≤ C := hC y hy
  calc t * ‖y‖ ≤ (δ / (C + 1)) * C :=
        mul_le_mul ht hyC (norm_nonneg y) (le_of_lt (div_pos hδ (by positivity)))
    _ < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [hδ, hC0]

/-! ### `DomIn` transports to a sub-cube chart -/

theorem domIn_subcube {X : Set M} {ψ χ : PL.CubeChart n M} {c : PL.E n} {t : ℝ} (ht : 0 < t)
    (hc : ∀ y ∈ PL.closedCube (n := n) 1, c + t • y ∈ PL.closedCube (n := n) 1)
    (hχ : ∀ y, χ.toFun y = ψ.toFun (c + t • y))
    (hDom : Work.Engulf.DomIn p ψ X) : Work.Engulf.DomIn p χ X := by
  obtain ⟨P, hP, hPx⟩ := hDom
  refine ⟨affSubSmul c t '' P, ?_, ?_⟩
  · exact Work.PL.Subdiv.DomDim.domDim_affine_image (affSubSmul c t)
      (affSubSmul_injective c (ne_of_gt ht)) hP
  · intro y hy1 hyX
    rw [hχ] at hyX
    have hy1' : c + t • y ∈ PL.closedCube (n := n) 1 := hc y hy1
    have hyP : c + t • y ∈ P := hPx (c + t • y) hy1' hyX
    exact ⟨c + t • y, hyP, affSubSmul_id c (ne_of_gt ht) y⟩

/-! ### `LinIn` transports to a sub-cube chart -/

theorem linIn_mono {f : PL.E N → M} {ψ : PL.CubeChart n M} {S S' : Set (PL.E N)} (h : S' ⊆ S)
    (hl : Work.Engulf.LinIn ψ f S) : Work.Engulf.LinIn ψ f S' := by
  obtain ⟨A, hA⟩ := hl
  exact ⟨A, fun z hz => hA z (h hz)⟩

theorem linIn_subcube {f : PL.E N → M} {ψ χ : PL.CubeChart n M} {c : PL.E n} {t : ℝ} (ht : 0 < t)
    (hχ : ∀ y, χ.toFun y = ψ.toFun (c + t • y)) {A : PL.E N →ᵃ[ℝ] PL.E n} {U : Set (PL.E N)}
    (hA : ∀ z ∈ U, ∃ w ∈ PL.openCube (n := n) 1, A z = c + t • w)
    (hAf : ∀ z ∈ U, f z = ψ.toFun (A z)) :
    Work.Engulf.LinIn χ f U := by
  refine ⟨(affSubSmul c t).comp A, fun z hz => ?_⟩
  obtain ⟨w, hw, hwz⟩ := hA z hz
  constructor
  · rw [AffineMap.comp_apply, affSubSmul_apply, hwz]
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
    exact hw
  · rw [AffineMap.comp_apply, affSubSmul_apply, hχ]
    have key : c + t • (t⁻¹ • (A z - c)) = A z := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul, add_sub_cancel]
    rw [key]
    exact hAf z hz

theorem linIn_subcube_shrink {f : PL.E N → M} {ψ χ : PL.CubeChart n M} {c : PL.E n} {t : ℝ}
    (ht : 0 < t) (hχ : ∀ y, χ.toFun y = ψ.toFun (c + t • y))
    {A : PL.E N →ᵃ[ℝ] PL.E n} {S0 : Set (PL.E N)} {y : PL.E N}
    (hAlin : ∀ z ∈ S0, A z ∈ PL.openCube (n := n) 1 ∧ f z = ψ.toFun (A z))
    (hAy : A y ∈ (fun w : PL.E n => c + t • w) '' PL.openCube (n := n) 1) :
    ∃ δ > 0, Work.Engulf.LinIn χ f (S0 ∩ ball y δ) := by
  have hopen := isOpen_affineImage_openCube (n := n) (c := c) ht
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen (A y) hAy
  have hcontA : Continuous A := A.continuous_of_finiteDimensional
  obtain ⟨δ, hδ, hδsub⟩ := Metric.continuous_iff.mp hcontA y ε hε
  refine ⟨δ, hδ, linIn_subcube (A := A) ht hχ ?_ ?_⟩
  · intro z hz
    have hz2 : dist (A z) (A y) < ε := hδsub z hz.2
    obtain ⟨w, hw, hweq⟩ := hεsub hz2
    exact ⟨w, hw, hweq.symm⟩
  · intro z hz; exact (hAlin z hz.1).2

/-- **`tame_extend`** (Hx2d′, replacing Hx2d; `Submission/Work/NOTES_LEAD_poincare_E1fix.md` §1/§2): adding frozen faces `S` that are `ψ`-affine with image in the closed `ρ`-cube (`ρ < 3/4`) and whose image is *disjoint* from the image of the previously frozen part `L₁` keeps `Tame`; `ψ` needs to be a smoothing chart only for the frozen part `(L₀ ∪ S)`.  This is the corrected form: Hx2d as used in the first version of E1 took `ψ` smooth only for the *original* frozen set, which is where the shear counterexample of the repair note lives.  Proof: at `x ∈ f '' S` use the sub-chart `χ(y) = ψ(c + t y)` of `Work.Engulf.Aux.subcube_chart` with `x = ψ c`, `t = 3/4 - ρ`, and a ball around `x` missing the compact `f '' L₁`; at `x ∉ f '' S` use a `Tame` chart of the old configuration with `Tame`'s clause for `L₀ ∪ L₁`, shrunk by a sub-chart whose closed image misses the compact `f '' S`.  (`hfin` and `hcont` are load-bearing: they make `f '' S` and `f '' L₁` compact.) -/
theorem tame_extend {n p N : ℕ} {M : Type*} [MetricSpace M] {X : Set M} {Γ : PL.Cx N}
    {L₀ L₁ S : Set (PL.E N)} {f : PL.E N → M} (ψ : PL.CubeChart n M) {ρ : ℝ} (hρ : ρ < 3 / 4)
    (hfin : Γ.faces.Finite) (hcont : ContinuousOn f Γ.space) (hL₁ : Work.Engulf.IsSubSp Γ L₁)
    (hS : Work.Engulf.IsSubSp Γ S)
    (hsplit : ∀ s ∈ Γ.faces, PL.simp s ⊆ L₀ ∪ L₁ ∪ S →
      PL.simp s ⊆ L₀ ∨ PL.simp s ⊆ L₁ ∨ PL.simp s ⊆ S)
    (htame : Work.Engulf.Tame n p X Γ (L₀ ∪ L₁) f)
    (hψ : Work.Engulf.SmoothChart p X Γ (L₀ ∪ S) f ψ)
    (hSim : f '' S ⊆ ψ.toFun '' PL.closedCube ρ)
    (hdisj : Disjoint (f '' S) (f '' L₁)) :
    Work.Engulf.Tame n p X Γ (L₀ ∪ L₁ ∪ S) f := by
  intro x
  by_cases hxS : x ∈ f '' S
  · -- ## Case A: `x ∈ f '' S`
    obtain ⟨a, haS, hax⟩ := hxS
    obtain ⟨c, hcρ, hcx⟩ := hSim ⟨a, haS, rfl⟩
    have hψc : ψ.toFun c = x := hcx.trans hax
    have hKc : IsCompact (f '' L₁) := isCompact_image_of_isSubSp hfin hcont hL₁
    have hxnotK : x ∉ f '' L₁ := fun h => Set.disjoint_left.mp hdisj ⟨a, haS, hax⟩ h
    obtain ⟨η, hη, hdisjη⟩ := exists_ball_disjoint_of_isCompact hKc hxnotK
    have hc_open : c ∈ PL.openCube (n := n) 1 :=
      Work.Engulf.closedCube_subset_openCube (lt_trans hρ (by norm_num)) hcρ
    have hcontat : ContinuousAt ψ.toFun c :=
      ψ.cont.continuousAt ((Work.Engulf.isOpen_openCube 1).mem_nhds hc_open)
    obtain ⟨δc, hδc, hδcsub⟩ := Metric.continuousAt_iff.mp hcontat η hη
    obtain ⟨t₀, ht₀pos, ht₀ball⟩ := exists_pos_smul_closedCube_subset_ball (n := n) hδc
    set t : ℝ := min (3 / 4 - ρ) t₀ with htdef
    have htpos : 0 < t := by rw [htdef]; exact lt_min (by linarith) ht₀pos
    have htle : t ≤ 3 / 4 - ρ := by rw [htdef]; exact min_le_left _ _
    have htle₀ : t ≤ t₀ := by rw [htdef]; exact min_le_right _ _
    have ht0 : 0 ≤ t := le_of_lt htpos
    have hcsub : ∀ y ∈ PL.closedCube (n := n) 1, c + t • y ∈ PL.openCube (n := n) 1 :=
      subcube_maps_closedCube_open (ρ := ρ) (r := 1) (r' := 1) hcρ ht0 (by linarith)
    have h3 : ∀ z ∈ PL.closedCube (n := n) (3 / 4),
        c + t • z ∈ PL.closedCube (n := n) (3 / 4) :=
      subcube_maps_closedCube (ρ := ρ) (r := 3 / 4) (r' := 3 / 4) hcρ ht0 (by linarith)
    obtain ⟨χ, hχ⟩ := subcube_chart ψ c htpos hcsub
    have hDomχ : Work.Engulf.DomIn p χ X :=
      domIn_subcube (X := X) htpos
        (fun y hy => Work.Engulf.openCube_subset_closedCube 1 (hcsub y hy)) hχ hψ.1
    have hxχ : x ∈ χ.toFun '' PL.openCube (n := n) (1 / 2) := by
      refine ⟨0, by intro i; simp, ?_⟩
      rw [hχ]; simp only [smul_zero, add_zero]; exact hψc
    refine ⟨χ, hxχ, hDomχ, ?_⟩
    intro s hs hsubAll y hy hycube
    have go : PL.simp s ⊆ L₀ ∪ S → ∃ δ > 0, Work.Engulf.LinIn χ f (PL.simp s ∩ ball y δ) := by
      intro hsubLS
      have hcubeψ : f y ∈ ψ.toFun '' PL.closedCube (n := n) (3 / 4) := by
        obtain ⟨z, hz, hzχ⟩ := hycube
        exact ⟨c + t • z, h3 z hz, by rw [← hzχ, hχ]⟩
      obtain ⟨δ, hδ, hlin⟩ := hψ.2 s hs hsubLS y hy hcubeψ
      obtain ⟨A, hAlin⟩ := hlin
      have hy' : y ∈ PL.simp s ∩ ball y δ := ⟨hy, mem_ball_self hδ⟩
      have hAy : A y ∈ (fun w : PL.E n => c + t • w) '' PL.openCube (n := n) 1 := by
        obtain ⟨z, hz, hzχ⟩ := hycube
        exact ⟨z, Work.Engulf.closedCube_subset_openCube (by norm_num) hz,
          CubeChart.injOn_openCube ψ
            (Work.Engulf.closedCube_subset_openCube (by norm_num) (h3 z hz))
            (hAlin y hy').1 (((hχ z).symm.trans hzχ).trans (hAlin y hy').2)⟩
      obtain ⟨δ', hδ', hlinχ⟩ := linIn_subcube_shrink htpos hχ hAlin hAy
      refine ⟨min δ δ', lt_min hδ hδ', ?_⟩
      have hsubmin : PL.simp s ∩ ball y (min δ δ') ⊆ (PL.simp s ∩ ball y δ) ∩ ball y δ' :=
        fun z hz => ⟨⟨hz.1, Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz.2) (min_le_left _ _))⟩,
          Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz.2) (min_le_right _ _))⟩
      exact linIn_mono hsubmin hlinχ
    rcases hsplit s hs hsubAll with hsL0 | hsL1 | hsS
    · exact go (Set.Subset.trans hsL0 Set.subset_union_left)
    · exfalso
      obtain ⟨z, hz, hzχ⟩ := hycube
      have hz1 : z ∈ PL.closedCube (n := n) 1 := Work.Engulf.closedCube_mono (by norm_num) hz
      have hdist : dist (c + t • z) c < δc := ht₀ball t ht0 htle₀ z hz1
      have hψball : ψ.toFun (c + t • z) ∈ ball x η := by
        have h1 := hδcsub hdist
        rwa [hψc] at h1
      have hfyball : f y ∈ ball x η := by rw [← hzχ, hχ]; exact hψball
      have hfyK : f y ∈ f '' L₁ := ⟨y, hsL1 hy, rfl⟩
      exact (Set.disjoint_left.mp hdisjη hfyball) hfyK
    · exact go (Set.Subset.trans hsS Set.subset_union_right)
  · -- ## Case B: `x ∉ f '' S`
    obtain ⟨ψx, hxmem, hψxsmooth⟩ := htame x
    obtain ⟨c, hc12, hcψx⟩ := hxmem
    have hKc : IsCompact (f '' S) := isCompact_image_of_isSubSp hfin hcont hS
    obtain ⟨η, hη, hdisjη⟩ := exists_ball_disjoint_of_isCompact hKc hxS
    have hc_open : c ∈ PL.openCube (n := n) 1 :=
      Work.Engulf.openCube_mono (by norm_num) hc12
    have hcontat : ContinuousAt ψx.toFun c :=
      ψx.cont.continuousAt ((Work.Engulf.isOpen_openCube 1).mem_nhds hc_open)
    obtain ⟨δc, hδc, hδcsub⟩ := Metric.continuousAt_iff.mp hcontat η hη
    obtain ⟨t₀, ht₀pos, ht₀ball⟩ := exists_pos_smul_closedCube_subset_ball (n := n) hδc
    set t : ℝ := min (1 / 3) t₀ with htdef
    have htpos : 0 < t := by rw [htdef]; exact lt_min (by norm_num) ht₀pos
    have htle : t ≤ 1 / 3 := by rw [htdef]; exact min_le_left _ _
    have htle₀ : t ≤ t₀ := by rw [htdef]; exact min_le_right _ _
    have ht0 : 0 ≤ t := le_of_lt htpos
    have hchalf : c ∈ PL.closedCube (n := n) (1 / 2) := fun i => le_of_lt (hc12 i)
    have hcsub : ∀ y ∈ PL.closedCube (n := n) 1, c + t • y ∈ PL.openCube (n := n) 1 :=
      subcube_maps_closedCube_open (ρ := 1 / 2) (r := 1) (r' := 1) hchalf ht0 (by linarith)
    have h3 : ∀ z ∈ PL.closedCube (n := n) (3 / 4),
        c + t • z ∈ PL.closedCube (n := n) (3 / 4) :=
      subcube_maps_closedCube (ρ := 1 / 2) (r := 3 / 4) (r' := 3 / 4) hchalf ht0 (by linarith)
    obtain ⟨χ, hχ⟩ := subcube_chart ψx c htpos hcsub
    have hDomχ : Work.Engulf.DomIn p χ X :=
      domIn_subcube (X := X) htpos
        (fun y hy => Work.Engulf.openCube_subset_closedCube 1 (hcsub y hy)) hχ hψxsmooth.1
    have hxχ : x ∈ χ.toFun '' PL.openCube (n := n) (1 / 2) := by
      refine ⟨0, by intro i; simp, ?_⟩
      rw [hχ]; simp only [smul_zero, add_zero]; exact hcψx
    refine ⟨χ, hxχ, hDomχ, ?_⟩
    intro s hs hsubAll y hy hycube
    have go : PL.simp s ⊆ L₀ ∪ L₁ → ∃ δ > 0, Work.Engulf.LinIn χ f (PL.simp s ∩ ball y δ) := by
      intro hsubLS
      have hcubeψ : f y ∈ ψx.toFun '' PL.closedCube (n := n) (3 / 4) := by
        obtain ⟨z, hz, hzχ⟩ := hycube
        exact ⟨c + t • z, h3 z hz, by rw [← hzχ, hχ]⟩
      obtain ⟨δ, hδ, hlin⟩ := hψxsmooth.2 s hs hsubLS y hy hcubeψ
      obtain ⟨A, hAlin⟩ := hlin
      have hy' : y ∈ PL.simp s ∩ ball y δ := ⟨hy, mem_ball_self hδ⟩
      have hAy : A y ∈ (fun w : PL.E n => c + t • w) '' PL.openCube (n := n) 1 := by
        obtain ⟨z, hz, hzχ⟩ := hycube
        exact ⟨z, Work.Engulf.closedCube_subset_openCube (by norm_num) hz,
          CubeChart.injOn_openCube ψx
            (Work.Engulf.closedCube_subset_openCube (by norm_num) (h3 z hz))
            (hAlin y hy').1 (((hχ z).symm.trans hzχ).trans (hAlin y hy').2)⟩
      obtain ⟨δ', hδ', hlinχ⟩ := linIn_subcube_shrink htpos hχ hAlin hAy
      refine ⟨min δ δ', lt_min hδ hδ', ?_⟩
      have hsubmin : PL.simp s ∩ ball y (min δ δ') ⊆ (PL.simp s ∩ ball y δ) ∩ ball y δ' :=
        fun z hz => ⟨⟨hz.1, Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz.2) (min_le_left _ _))⟩,
          Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz.2) (min_le_right _ _))⟩
      exact linIn_mono hsubmin hlinχ
    rcases hsplit s hs hsubAll with hsL0 | hsL1 | hsS
    · exact go (Set.Subset.trans hsL0 Set.subset_union_left)
    · exact go (Set.Subset.trans hsL1 Set.subset_union_right)
    · exfalso
      obtain ⟨z, hz, hzχ⟩ := hycube
      have hz1 : z ∈ PL.closedCube (n := n) 1 := Work.Engulf.closedCube_mono (by norm_num) hz
      have hdist : dist (c + t • z) c < δc := ht₀ball t ht0 htle₀ z hz1
      have hψball : ψx.toFun (c + t • z) ∈ ball x η := by
        have h1 := hδcsub hdist
        rwa [hcψx] at h1
      have hfyball : f y ∈ ball x η := by rw [← hzχ, hχ]; exact hψball
      have hfyS : f y ∈ f '' S := ⟨y, hsS hy, rfl⟩
      exact (Set.disjoint_left.mp hdisjη hfyball) hfyS

end Work.Engulf.Aux
